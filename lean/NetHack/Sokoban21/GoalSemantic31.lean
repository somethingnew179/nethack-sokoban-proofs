/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalSemantic30
import NetHack.Sokoban21.Debt
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open Diagram
theorem goal0_shape62 (g h i j k l : Bool) : d3274 (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape62 (g h i j k l : Bool) : d3277 (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape62 (g h i j k l : Bool) : d3279 (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape62 (g h i j k l : Bool) : d3280 (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape62 (g h i j k l : Bool) : d3292 (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨true,true,true,true,true,false,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal0_shape63 (g h i j k l : Bool) : d3274 (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (0 + (Projection.occupied (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal1_shape63 (g h i j k l : Bool) : d3277 (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (1 + (Projection.occupied (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal2_shape63 (g h i j k l : Bool) : d3279 (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (2 + (Projection.occupied (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem goal3_shape63 (g h i j k l : Bool) : d3280 (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve) = (if decide (3 + (Projection.occupied (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve)).length ≤ 3) then 1 else 0) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
theorem cap_shape63 (g h i j k l : Bool) : d3292 (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve) = min 6 (patternDebt (⟨true,true,true,true,true,true,g,h,i,j,k,l⟩ : Twelve)) := by
  cases g <;> cases h <;> cases i <;> cases j <;> cases k <;> cases l <;> rfl
end NetHack.Sokoban21
