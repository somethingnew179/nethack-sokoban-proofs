/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalSemantic16
import NetHack.Sokoban21.Debt
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open Diagram
theorem goal0_shape34 (g h i j k l : Bool) : d3274 (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape34 (g h i j k l : Bool) : d3277 (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape34 (g h i j k l : Bool) : d3279 (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape34 (g h i j k l : Bool) : d3280 (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape34 (g h i j k l : Bool) : d3292 (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨true,false,false,false,true,false,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal0_shape35 (g h i j k l : Bool) : d3274 (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape35 (g h i j k l : Bool) : d3277 (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape35 (g h i j k l : Bool) : d3279 (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape35 (g h i j k l : Bool) : d3280 (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape35 (g h i j k l : Bool) : d3292 (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨true,false,false,false,true,true,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
end NetHack.Sokoban21
