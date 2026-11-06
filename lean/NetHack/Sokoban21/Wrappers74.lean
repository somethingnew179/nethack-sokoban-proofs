/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers73
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_consume239_0 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume239_0 : ConsumeBound ⟨186,185,187,194,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume239_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume239_1 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume239_1 : ConsumeBound ⟨186,185,187,194,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume239_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume239_2 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume239_2 : ConsumeBound ⟨186,185,187,194,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume239_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume239_3 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume239_3 : ConsumeBound ⟨186,185,187,194,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume239_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume240_0 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume240_0 : ConsumeBound ⟨186,185,187,195,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume240_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume240_1 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume240_1 : ConsumeBound ⟨186,185,187,195,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume240_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume240_2 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume240_2 : ConsumeBound ⟨186,185,187,195,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume240_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume240_3 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume240_3 : ConsumeBound ⟨186,185,187,195,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume240_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume241_0 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume241_0 : ConsumeBound ⟨186,185,187,196,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume241_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume241_1 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume241_1 : ConsumeBound ⟨186,185,187,196,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume241_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume241_2 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume241_2 : ConsumeBound ⟨186,185,187,196,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume241_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume241_3 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume241_3 : ConsumeBound ⟨186,185,187,196,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume241_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume242_0 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume242_0 : ConsumeBound ⟨186,185,187,197,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume242_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume242_1 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume242_1 : ConsumeBound ⟨186,185,187,197,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume242_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume242_2 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume242_2 : ConsumeBound ⟨186,185,187,197,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume242_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume242_3 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume242_3 : ConsumeBound ⟨186,185,187,197,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume242_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume246_0 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume246_0 : ConsumeBound ⟨187,186,188,188,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume246_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume246_1 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume246_1 : ConsumeBound ⟨187,186,188,188,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume246_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume246_2 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume246_2 : ConsumeBound ⟨187,186,188,188,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume246_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume246_3 (pattern : Twelve) : pushGuard ⟨187,186,188,188,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume246_3 : ConsumeBound ⟨187,186,188,188,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume246_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume248_0 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume248_0 : ConsumeBound ⟨188,187,189,189,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume248_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume248_1 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume248_1 : ConsumeBound ⟨188,187,189,189,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume248_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume248_2 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume248_2 : ConsumeBound ⟨188,187,189,189,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume248_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume248_3 (pattern : Twelve) : pushGuard ⟨188,187,189,189,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume248_3 : ConsumeBound ⟨188,187,189,189,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume248_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume249_0 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume249_0 : ConsumeBound ⟨188,189,187,188,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume249_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume249_1 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume249_1 : ConsumeBound ⟨188,189,187,188,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume249_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume249_2 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume249_2 : ConsumeBound ⟨188,189,187,188,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume249_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume249_3 (pattern : Twelve) : pushGuard ⟨188,189,187,188,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume249_3 : ConsumeBound ⟨188,189,187,188,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume249_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume257_0 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume257_0 : ConsumeBound ⟨189,188,190,190,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume257_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume257_1 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume257_1 : ConsumeBound ⟨189,188,190,190,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume257_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume257_2 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume257_2 : ConsumeBound ⟨189,188,190,190,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume257_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume257_3 (pattern : Twelve) : pushGuard ⟨189,188,190,190,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume257_3 : ConsumeBound ⟨189,188,190,190,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume257_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume258_0 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume258_0 : ConsumeBound ⟨189,190,188,188,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume258_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume258_1 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume258_1 : ConsumeBound ⟨189,190,188,188,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume258_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume258_2 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume258_2 : ConsumeBound ⟨189,190,188,188,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume258_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume258_3 (pattern : Twelve) : pushGuard ⟨189,190,188,188,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume258_3 : ConsumeBound ⟨189,190,188,188,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume258_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume259_0 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume259_0 : ConsumeBound ⟨190,189,191,191,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume259_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume259_1 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume259_1 : ConsumeBound ⟨190,189,191,191,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume259_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume259_2 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume259_2 : ConsumeBound ⟨190,189,191,191,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume259_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume259_3 (pattern : Twelve) : pushGuard ⟨190,189,191,191,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume259_3 : ConsumeBound ⟨190,189,191,191,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume259_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume260_0 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume260_0 : ConsumeBound ⟨190,191,189,189,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume260_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume260_1 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume260_1 : ConsumeBound ⟨190,191,189,189,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume260_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume260_2 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume260_2 : ConsumeBound ⟨190,191,189,189,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume260_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume260_3 (pattern : Twelve) : pushGuard ⟨190,191,189,189,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume260_3 : ConsumeBound ⟨190,191,189,189,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume260_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume261_0 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume261_0 : ConsumeBound ⟨191,190,192,192,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume261_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume261_1 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume261_1 : ConsumeBound ⟨191,190,192,192,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume261_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume261_2 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume261_2 : ConsumeBound ⟨191,190,192,192,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume261_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume261_3 (pattern : Twelve) : pushGuard ⟨191,190,192,192,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume261_3 : ConsumeBound ⟨191,190,192,192,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume261_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume262_0 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume262_0 : ConsumeBound ⟨191,192,190,190,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume262_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume262_1 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume262_1 : ConsumeBound ⟨191,192,190,190,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume262_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
end NetHack.Sokoban21
