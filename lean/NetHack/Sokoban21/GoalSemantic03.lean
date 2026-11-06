/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalSemantic02
import NetHack.Sokoban21.Debt
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open Diagram
theorem goal0_shape6 (g h i j k l : Bool) : d3274 (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape6 (g h i j k l : Bool) : d3277 (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape6 (g h i j k l : Bool) : d3279 (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape6 (g h i j k l : Bool) : d3280 (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape6 (g h i j k l : Bool) : d3292 (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨false,false,false,true,true,false,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal0_shape7 (g h i j k l : Bool) : d3274 (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape7 (g h i j k l : Bool) : d3277 (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape7 (g h i j k l : Bool) : d3279 (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape7 (g h i j k l : Bool) : d3280 (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape7 (g h i j k l : Bool) : d3292 (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨false,false,false,true,true,true,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
end NetHack.Sokoban21
