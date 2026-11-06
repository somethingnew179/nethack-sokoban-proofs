/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers70
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push245_2 (pattern : Twelve) : pushGuard ⟨186,187,185,185,.west,2,19,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push245_2 : PushBound ⟨186,187,185,185,.west,2,19,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push245_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push245_3 (pattern : Twelve) : pushGuard ⟨186,187,185,185,.west,2,19,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push245_3 : PushBound ⟨186,187,185,185,.west,2,19,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push245_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push246_0 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push246_0 : PushBound ⟨187,186,188,188,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push246_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push246_1 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push246_1 : PushBound ⟨187,186,188,188,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push246_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push246_2 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push246_2 : PushBound ⟨187,186,188,188,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push246_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push246_3 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push246_3 : PushBound ⟨187,186,188,188,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push246_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push247_0 (pattern : Twelve) : pushGuard ⟨187,188,186,186,.west,1,19,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push247_0 : PushBound ⟨187,188,186,186,.west,1,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push247_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push247_1 (pattern : Twelve) : pushGuard ⟨187,188,186,186,.west,1,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push247_1 : PushBound ⟨187,188,186,186,.west,1,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push247_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push247_2 (pattern : Twelve) : pushGuard ⟨187,188,186,186,.west,1,19,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push247_2 : PushBound ⟨187,188,186,186,.west,1,19,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push247_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push247_3 (pattern : Twelve) : pushGuard ⟨187,188,186,186,.west,1,19,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push247_3 : PushBound ⟨187,188,186,186,.west,1,19,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push247_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push248_0 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push248_0 : PushBound ⟨188,187,189,189,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push248_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push248_1 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push248_1 : PushBound ⟨188,187,189,189,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push248_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push248_2 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push248_2 : PushBound ⟨188,187,189,189,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push248_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push248_3 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push248_3 : PushBound ⟨188,187,189,189,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push248_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push249_0 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push249_0 : PushBound ⟨188,189,187,188,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push249_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push249_1 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push249_1 : PushBound ⟨188,189,187,188,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push249_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push249_2 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push249_2 : PushBound ⟨188,189,187,188,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push249_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push249_3 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push249_3 : PushBound ⟨188,189,187,188,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push249_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push250_0 (pattern : Twelve) : pushGuard ⟨188,189,187,187,.west,2,20,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push250_0 : PushBound ⟨188,189,187,187,.west,2,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push250_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push250_1 (pattern : Twelve) : pushGuard ⟨188,189,187,187,.west,2,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push250_1 : PushBound ⟨188,189,187,187,.west,2,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push250_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push250_2 (pattern : Twelve) : pushGuard ⟨188,189,187,187,.west,2,20,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push250_2 : PushBound ⟨188,189,187,187,.west,2,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push250_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push250_3 (pattern : Twelve) : pushGuard ⟨188,189,187,187,.west,2,20,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push250_3 : PushBound ⟨188,189,187,187,.west,2,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push250_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push251_0 (pattern : Twelve) : pushGuard ⟨188,189,187,186,.west,2,20,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push251_0 : PushBound ⟨188,189,187,186,.west,2,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push251_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push251_1 (pattern : Twelve) : pushGuard ⟨188,189,187,186,.west,2,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push251_1 : PushBound ⟨188,189,187,186,.west,2,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push251_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push251_2 (pattern : Twelve) : pushGuard ⟨188,189,187,186,.west,2,20,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push251_2 : PushBound ⟨188,189,187,186,.west,2,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push251_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push251_3 (pattern : Twelve) : pushGuard ⟨188,189,187,186,.west,2,20,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push251_3 : PushBound ⟨188,189,187,186,.west,2,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push251_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push252_0 (pattern : Twelve) : pushGuard ⟨188,189,187,185,.west,3,20,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push252_0 : PushBound ⟨188,189,187,185,.west,3,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push252_0]; exact allowed)
  have checked := c22607 pattern guarded
  change d806 pattern ≤ (3 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push252_1 (pattern : Twelve) : pushGuard ⟨188,189,187,185,.west,3,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push252_1 : PushBound ⟨188,189,187,185,.west,3,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push252_1]; exact allowed)
  have checked := c22608 pattern guarded
  change d1267 pattern ≤ (3 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push252_2 (pattern : Twelve) : pushGuard ⟨188,189,187,185,.west,3,20,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push252_2 : PushBound ⟨188,189,187,185,.west,3,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push252_2]; exact allowed)
  have checked := c22609 pattern guarded
  change d1636 pattern ≤ (3 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push252_3 (pattern : Twelve) : pushGuard ⟨188,189,187,185,.west,3,20,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push252_3 : PushBound ⟨188,189,187,185,.west,3,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push252_3]; exact allowed)
  have checked := c22610 pattern guarded
  change d1827 pattern ≤ (3 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push253_0 (pattern : Twelve) : pushGuard ⟨188,189,187,184,.west,4,20,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push253_0 : PushBound ⟨188,189,187,184,.west,4,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push253_0]; exact allowed)
  have checked := c22611 pattern guarded
  change d806 pattern ≤ (4 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push253_1 (pattern : Twelve) : pushGuard ⟨188,189,187,184,.west,4,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push253_1 : PushBound ⟨188,189,187,184,.west,4,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push253_1]; exact allowed)
  have checked := c22612 pattern guarded
  change d1267 pattern ≤ (4 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push253_2 (pattern : Twelve) : pushGuard ⟨188,189,187,184,.west,4,20,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push253_2 : PushBound ⟨188,189,187,184,.west,4,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push253_2]; exact allowed)
  have checked := c22613 pattern guarded
  change d1636 pattern ≤ (4 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push253_3 (pattern : Twelve) : pushGuard ⟨188,189,187,184,.west,4,20,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push253_3 : PushBound ⟨188,189,187,184,.west,4,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push253_3]; exact allowed)
  have checked := c22614 pattern guarded
  change d1827 pattern ≤ (4 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push254_0 (pattern : Twelve) : pushGuard ⟨188,189,187,183,.west,5,20,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push254_0 : PushBound ⟨188,189,187,183,.west,5,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push254_0]; exact allowed)
  have checked := c22737 pattern guarded
  change d806 pattern ≤ (5 : Int) + d806 (change pattern 12 0)
  rw [s7279]
  exact checked
theorem guard_push254_1 (pattern : Twelve) : pushGuard ⟨188,189,187,183,.west,5,20,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push254_1 : PushBound ⟨188,189,187,183,.west,5,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push254_1]; exact allowed)
  have checked := c22814 pattern guarded
  change d1267 pattern ≤ (5 : Int) + d1267 (change pattern 12 0)
  rw [s7334]
  exact checked
theorem guard_push254_2 (pattern : Twelve) : pushGuard ⟨188,189,187,183,.west,5,20,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push254_2 : PushBound ⟨188,189,187,183,.west,5,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push254_2]; exact allowed)
  have checked := c22900 pattern guarded
  change d1636 pattern ≤ (5 : Int) + d1636 (change pattern 12 0)
  rw [s7385]
  exact checked
theorem guard_push254_3 (pattern : Twelve) : pushGuard ⟨188,189,187,183,.west,5,20,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push254_3 : PushBound ⟨188,189,187,183,.west,5,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push254_3]; exact allowed)
  have checked := c22953 pattern guarded
  change d1827 pattern ≤ (5 : Int) + d1827 (change pattern 12 0)
  rw [s7413]
  exact checked
theorem guard_push255_0 (pattern : Twelve) : pushGuard ⟨188,189,187,182,.west,6,20,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push255_0 : PushBound ⟨188,189,187,182,.west,6,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push255_0]; exact allowed)
  have checked := c22954 pattern guarded
  change d806 pattern ≤ (6 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push255_1 (pattern : Twelve) : pushGuard ⟨188,189,187,182,.west,6,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push255_1 : PushBound ⟨188,189,187,182,.west,6,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push255_1]; exact allowed)
  have checked := c22955 pattern guarded
  change d1267 pattern ≤ (6 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push255_2 (pattern : Twelve) : pushGuard ⟨188,189,187,182,.west,6,20,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push255_2 : PushBound ⟨188,189,187,182,.west,6,20,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push255_2]; exact allowed)
  have checked := c22956 pattern guarded
  change d1636 pattern ≤ (6 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push255_3 (pattern : Twelve) : pushGuard ⟨188,189,187,182,.west,6,20,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push255_3 : PushBound ⟨188,189,187,182,.west,6,20,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push255_3]; exact allowed)
  have checked := c22957 pattern guarded
  change d1827 pattern ≤ (6 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push256_0 (pattern : Twelve) : pushGuard ⟨188,189,187,181,.west,20,20,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push256_0 : PushBound ⟨188,189,187,181,.west,20,20,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push256_0]; exact allowed)
  have checked := c23189 pattern guarded
  change d806 pattern ≤ (20 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push256_1 (pattern : Twelve) : pushGuard ⟨188,189,187,181,.west,20,20,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push256_1 : PushBound ⟨188,189,187,181,.west,20,20,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push256_1]; exact allowed)
  have checked := c23333 pattern guarded
  change d1267 pattern ≤ (20 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push256_2 (pattern : Twelve) : pushGuard ⟨188,189,187,181,.west,20,20,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push256_2 : PushBound ⟨188,189,187,181,.west,20,20,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push256_2]; exact allowed)
  have checked := c23436 pattern guarded
  change d1636 pattern ≤ (20 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push256_3 (pattern : Twelve) : pushGuard ⟨188,189,187,181,.west,20,20,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push256_3 : PushBound ⟨188,189,187,181,.west,20,20,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push256_3]; exact allowed)
  have checked := c23490 pattern guarded
  change d1827 pattern ≤ (20 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push257_0 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push257_0 : PushBound ⟨189,188,190,190,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push257_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push257_1 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push257_1 : PushBound ⟨189,188,190,190,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push257_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push257_2 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push257_2 : PushBound ⟨189,188,190,190,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push257_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push257_3 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push257_3 : PushBound ⟨189,188,190,190,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push257_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
end NetHack.Sokoban21
