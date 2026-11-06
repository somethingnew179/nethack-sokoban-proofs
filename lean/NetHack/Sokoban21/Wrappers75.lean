/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers74
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_consume262_2 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume262_2 : ConsumeBound ⟨191,192,190,190,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume262_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume262_3 (pattern : Twelve) : pushGuard ⟨191,192,190,190,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume262_3 : ConsumeBound ⟨191,192,190,190,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume262_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume263_0 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume263_0 : ConsumeBound ⟨192,191,193,193,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume263_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume263_1 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume263_1 : ConsumeBound ⟨192,191,193,193,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume263_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume263_2 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume263_2 : ConsumeBound ⟨192,191,193,193,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume263_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume263_3 (pattern : Twelve) : pushGuard ⟨192,191,193,193,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume263_3 : ConsumeBound ⟨192,191,193,193,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume263_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume264_0 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume264_0 : ConsumeBound ⟨192,193,191,191,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume264_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume264_1 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume264_1 : ConsumeBound ⟨192,193,191,191,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume264_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume264_2 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume264_2 : ConsumeBound ⟨192,193,191,191,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume264_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume264_3 (pattern : Twelve) : pushGuard ⟨192,193,191,191,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume264_3 : ConsumeBound ⟨192,193,191,191,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume264_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume265_0 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume265_0 : ConsumeBound ⟨193,192,194,194,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume265_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume265_1 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume265_1 : ConsumeBound ⟨193,192,194,194,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume265_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume265_2 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume265_2 : ConsumeBound ⟨193,192,194,194,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume265_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume265_3 (pattern : Twelve) : pushGuard ⟨193,192,194,194,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume265_3 : ConsumeBound ⟨193,192,194,194,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume265_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume266_0 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume266_0 : ConsumeBound ⟨193,194,192,192,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume266_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume266_1 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume266_1 : ConsumeBound ⟨193,194,192,192,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume266_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume266_2 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume266_2 : ConsumeBound ⟨193,194,192,192,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume266_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume266_3 (pattern : Twelve) : pushGuard ⟨193,194,192,192,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume266_3 : ConsumeBound ⟨193,194,192,192,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume266_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume267_0 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume267_0 : ConsumeBound ⟨194,193,195,195,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume267_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume267_1 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume267_1 : ConsumeBound ⟨194,193,195,195,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume267_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume267_2 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume267_2 : ConsumeBound ⟨194,193,195,195,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume267_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume267_3 (pattern : Twelve) : pushGuard ⟨194,193,195,195,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume267_3 : ConsumeBound ⟨194,193,195,195,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume267_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume268_0 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume268_0 : ConsumeBound ⟨194,195,193,193,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume268_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume268_1 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume268_1 : ConsumeBound ⟨194,195,193,193,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume268_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume268_2 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume268_2 : ConsumeBound ⟨194,195,193,193,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume268_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume268_3 (pattern : Twelve) : pushGuard ⟨194,195,193,193,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume268_3 : ConsumeBound ⟨194,195,193,193,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume268_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume269_0 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume269_0 : ConsumeBound ⟨195,194,196,196,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume269_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume269_1 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume269_1 : ConsumeBound ⟨195,194,196,196,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume269_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume269_2 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume269_2 : ConsumeBound ⟨195,194,196,196,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume269_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume269_3 (pattern : Twelve) : pushGuard ⟨195,194,196,196,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume269_3 : ConsumeBound ⟨195,194,196,196,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume269_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume270_0 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume270_0 : ConsumeBound ⟨195,196,194,194,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume270_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume270_1 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume270_1 : ConsumeBound ⟨195,196,194,194,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume270_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume270_2 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume270_2 : ConsumeBound ⟨195,196,194,194,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume270_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume270_3 (pattern : Twelve) : pushGuard ⟨195,196,194,194,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume270_3 : ConsumeBound ⟨195,196,194,194,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume270_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume271_0 (pattern : Twelve) : pushGuard ⟨196,195,197,197,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume271_0 : ConsumeBound ⟨196,195,197,197,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume271_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume271_1 (pattern : Twelve) : pushGuard ⟨196,195,197,197,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume271_1 : ConsumeBound ⟨196,195,197,197,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume271_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume271_2 (pattern : Twelve) : pushGuard ⟨196,195,197,197,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume271_2 : ConsumeBound ⟨196,195,197,197,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume271_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume271_3 (pattern : Twelve) : pushGuard ⟨196,195,197,197,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume271_3 : ConsumeBound ⟨196,195,197,197,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume271_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume272_0 (pattern : Twelve) : pushGuard ⟨196,197,195,195,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume272_0 : ConsumeBound ⟨196,197,195,195,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume272_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume272_1 (pattern : Twelve) : pushGuard ⟨196,197,195,195,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume272_1 : ConsumeBound ⟨196,197,195,195,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume272_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume272_2 (pattern : Twelve) : pushGuard ⟨196,197,195,195,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume272_2 : ConsumeBound ⟨196,197,195,195,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume272_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume272_3 (pattern : Twelve) : pushGuard ⟨196,197,195,195,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume272_3 : ConsumeBound ⟨196,197,195,195,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume272_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_consume274_0 (pattern : Twelve) : pushGuard ⟨197,198,196,196,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume274_0 : ConsumeBound ⟨197,198,196,196,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume274_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_consume274_1 (pattern : Twelve) : pushGuard ⟨197,198,196,196,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume274_1 : ConsumeBound ⟨197,198,196,196,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume274_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_consume274_2 (pattern : Twelve) : pushGuard ⟨197,198,196,196,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume274_2 : ConsumeBound ⟨197,198,196,196,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume274_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_consume274_3 (pattern : Twelve) : pushGuard ⟨197,198,196,196,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem consume274_3 : ConsumeBound ⟨197,198,196,196,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume274_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
end NetHack.Sokoban21
