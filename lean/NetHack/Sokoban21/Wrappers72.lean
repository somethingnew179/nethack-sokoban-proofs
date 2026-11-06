/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers71
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push258_0 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push258_0 : PushBound ⟨189,190,188,188,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push258_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push258_1 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push258_1 : PushBound ⟨189,190,188,188,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push258_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push258_2 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push258_2 : PushBound ⟨189,190,188,188,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push258_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push258_3 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push258_3 : PushBound ⟨189,190,188,188,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push258_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push259_0 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push259_0 : PushBound ⟨190,189,191,191,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push259_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push259_1 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push259_1 : PushBound ⟨190,189,191,191,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push259_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push259_2 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push259_2 : PushBound ⟨190,189,191,191,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push259_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push259_3 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push259_3 : PushBound ⟨190,189,191,191,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push259_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push260_0 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push260_0 : PushBound ⟨190,191,189,189,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push260_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push260_1 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push260_1 : PushBound ⟨190,191,189,189,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push260_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push260_2 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push260_2 : PushBound ⟨190,191,189,189,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push260_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push260_3 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push260_3 : PushBound ⟨190,191,189,189,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push260_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push261_0 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push261_0 : PushBound ⟨191,190,192,192,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push261_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push261_1 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push261_1 : PushBound ⟨191,190,192,192,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push261_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push261_2 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push261_2 : PushBound ⟨191,190,192,192,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push261_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push261_3 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push261_3 : PushBound ⟨191,190,192,192,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push261_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push262_0 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push262_0 : PushBound ⟨191,192,190,190,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push262_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push262_1 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push262_1 : PushBound ⟨191,192,190,190,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push262_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push262_2 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push262_2 : PushBound ⟨191,192,190,190,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push262_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push262_3 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push262_3 : PushBound ⟨191,192,190,190,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push262_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push263_0 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push263_0 : PushBound ⟨192,191,193,193,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push263_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push263_1 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push263_1 : PushBound ⟨192,191,193,193,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push263_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push263_2 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push263_2 : PushBound ⟨192,191,193,193,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push263_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push263_3 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push263_3 : PushBound ⟨192,191,193,193,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push263_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push264_0 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push264_0 : PushBound ⟨192,193,191,191,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push264_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push264_1 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push264_1 : PushBound ⟨192,193,191,191,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push264_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push264_2 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push264_2 : PushBound ⟨192,193,191,191,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push264_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push264_3 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push264_3 : PushBound ⟨192,193,191,191,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push264_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push265_0 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push265_0 : PushBound ⟨193,192,194,194,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push265_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push265_1 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push265_1 : PushBound ⟨193,192,194,194,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push265_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push265_2 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push265_2 : PushBound ⟨193,192,194,194,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push265_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push265_3 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push265_3 : PushBound ⟨193,192,194,194,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push265_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push266_0 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push266_0 : PushBound ⟨193,194,192,192,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push266_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push266_1 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push266_1 : PushBound ⟨193,194,192,192,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push266_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push266_2 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push266_2 : PushBound ⟨193,194,192,192,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push266_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push266_3 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push266_3 : PushBound ⟨193,194,192,192,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push266_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push267_0 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push267_0 : PushBound ⟨194,193,195,195,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push267_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push267_1 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push267_1 : PushBound ⟨194,193,195,195,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push267_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push267_2 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push267_2 : PushBound ⟨194,193,195,195,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push267_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push267_3 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push267_3 : PushBound ⟨194,193,195,195,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push267_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push268_0 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push268_0 : PushBound ⟨194,195,193,193,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push268_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push268_1 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push268_1 : PushBound ⟨194,195,193,193,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push268_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push268_2 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push268_2 : PushBound ⟨194,195,193,193,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push268_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push268_3 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push268_3 : PushBound ⟨194,195,193,193,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push268_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push269_0 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push269_0 : PushBound ⟨195,194,196,196,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push269_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push269_1 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push269_1 : PushBound ⟨195,194,196,196,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push269_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push269_2 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push269_2 : PushBound ⟨195,194,196,196,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push269_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push269_3 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push269_3 : PushBound ⟨195,194,196,196,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push269_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push270_0 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push270_0 : PushBound ⟨195,196,194,194,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push270_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push270_1 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push270_1 : PushBound ⟨195,196,194,194,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push270_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
end NetHack.Sokoban21
