/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers69
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push233_0 (pattern : Twelve) : pushGuard ⟨186,185,187,188,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push233_0 : PushBound ⟨186,185,187,188,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push233_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push233_1 (pattern : Twelve) : pushGuard ⟨186,185,187,188,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push233_1 : PushBound ⟨186,185,187,188,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push233_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push233_2 (pattern : Twelve) : pushGuard ⟨186,185,187,188,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push233_2 : PushBound ⟨186,185,187,188,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push233_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push233_3 (pattern : Twelve) : pushGuard ⟨186,185,187,188,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push233_3 : PushBound ⟨186,185,187,188,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push233_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push234_0 (pattern : Twelve) : pushGuard ⟨186,185,187,189,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push234_0 : PushBound ⟨186,185,187,189,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push234_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push234_1 (pattern : Twelve) : pushGuard ⟨186,185,187,189,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push234_1 : PushBound ⟨186,185,187,189,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push234_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push234_2 (pattern : Twelve) : pushGuard ⟨186,185,187,189,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push234_2 : PushBound ⟨186,185,187,189,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push234_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push234_3 (pattern : Twelve) : pushGuard ⟨186,185,187,189,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push234_3 : PushBound ⟨186,185,187,189,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push234_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push235_0 (pattern : Twelve) : pushGuard ⟨186,185,187,190,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push235_0 : PushBound ⟨186,185,187,190,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push235_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push235_1 (pattern : Twelve) : pushGuard ⟨186,185,187,190,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push235_1 : PushBound ⟨186,185,187,190,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push235_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push235_2 (pattern : Twelve) : pushGuard ⟨186,185,187,190,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push235_2 : PushBound ⟨186,185,187,190,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push235_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push235_3 (pattern : Twelve) : pushGuard ⟨186,185,187,190,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push235_3 : PushBound ⟨186,185,187,190,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push235_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push236_0 (pattern : Twelve) : pushGuard ⟨186,185,187,191,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push236_0 : PushBound ⟨186,185,187,191,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push236_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push236_1 (pattern : Twelve) : pushGuard ⟨186,185,187,191,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push236_1 : PushBound ⟨186,185,187,191,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push236_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push236_2 (pattern : Twelve) : pushGuard ⟨186,185,187,191,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push236_2 : PushBound ⟨186,185,187,191,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push236_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push236_3 (pattern : Twelve) : pushGuard ⟨186,185,187,191,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push236_3 : PushBound ⟨186,185,187,191,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push236_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push237_0 (pattern : Twelve) : pushGuard ⟨186,185,187,192,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push237_0 : PushBound ⟨186,185,187,192,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push237_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push237_1 (pattern : Twelve) : pushGuard ⟨186,185,187,192,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push237_1 : PushBound ⟨186,185,187,192,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push237_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push237_2 (pattern : Twelve) : pushGuard ⟨186,185,187,192,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push237_2 : PushBound ⟨186,185,187,192,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push237_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push237_3 (pattern : Twelve) : pushGuard ⟨186,185,187,192,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push237_3 : PushBound ⟨186,185,187,192,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push237_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push238_0 (pattern : Twelve) : pushGuard ⟨186,185,187,193,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push238_0 : PushBound ⟨186,185,187,193,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push238_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push238_1 (pattern : Twelve) : pushGuard ⟨186,185,187,193,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push238_1 : PushBound ⟨186,185,187,193,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push238_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push238_2 (pattern : Twelve) : pushGuard ⟨186,185,187,193,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push238_2 : PushBound ⟨186,185,187,193,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push238_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push238_3 (pattern : Twelve) : pushGuard ⟨186,185,187,193,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push238_3 : PushBound ⟨186,185,187,193,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push238_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push239_0 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push239_0 : PushBound ⟨186,185,187,194,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push239_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push239_1 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push239_1 : PushBound ⟨186,185,187,194,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push239_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push239_2 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push239_2 : PushBound ⟨186,185,187,194,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push239_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push239_3 (pattern : Twelve) : pushGuard ⟨186,185,187,194,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push239_3 : PushBound ⟨186,185,187,194,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push239_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push240_0 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push240_0 : PushBound ⟨186,185,187,195,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push240_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push240_1 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push240_1 : PushBound ⟨186,185,187,195,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push240_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push240_2 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push240_2 : PushBound ⟨186,185,187,195,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push240_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push240_3 (pattern : Twelve) : pushGuard ⟨186,185,187,195,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push240_3 : PushBound ⟨186,185,187,195,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push240_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push241_0 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push241_0 : PushBound ⟨186,185,187,196,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push241_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push241_1 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push241_1 : PushBound ⟨186,185,187,196,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push241_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push241_2 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push241_2 : PushBound ⟨186,185,187,196,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push241_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push241_3 (pattern : Twelve) : pushGuard ⟨186,185,187,196,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push241_3 : PushBound ⟨186,185,187,196,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push241_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push242_0 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push242_0 : PushBound ⟨186,185,187,197,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push242_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push242_1 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push242_1 : PushBound ⟨186,185,187,197,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push242_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push242_2 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push242_2 : PushBound ⟨186,185,187,197,.east,0,0,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push242_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push242_3 (pattern : Twelve) : pushGuard ⟨186,185,187,197,.east,0,0,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push242_3 : PushBound ⟨186,185,187,197,.east,0,0,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push242_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push243_0 (pattern : Twelve) : pushGuard ⟨186,185,187,198,.east,19,19,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push243_0 : PushBound ⟨186,185,187,198,.east,19,19,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push243_0]; exact allowed)
  have checked := c22305 pattern guarded
  change d806 pattern ≤ (19 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push243_1 (pattern : Twelve) : pushGuard ⟨186,185,187,198,.east,19,19,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push243_1 : PushBound ⟨186,185,187,198,.east,19,19,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push243_1]; exact allowed)
  have checked := c22449 pattern guarded
  change d1267 pattern ≤ (19 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push243_2 (pattern : Twelve) : pushGuard ⟨186,185,187,198,.east,19,19,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push243_2 : PushBound ⟨186,185,187,198,.east,19,19,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push243_2]; exact allowed)
  have checked := c22552 pattern guarded
  change d1636 pattern ≤ (19 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push243_3 (pattern : Twelve) : pushGuard ⟨186,185,187,198,.east,19,19,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push243_3 : PushBound ⟨186,185,187,198,.east,19,19,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push243_3]; exact allowed)
  have checked := c22606 pattern guarded
  change d1827 pattern ≤ (19 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push244_0 (pattern : Twelve) : pushGuard ⟨186,166,206,206,.south,19,19,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push244_0 : PushBound ⟨186,166,206,206,.south,19,19,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push244_0]; exact allowed)
  have checked := c22305 pattern guarded
  change d806 pattern ≤ (19 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push244_1 (pattern : Twelve) : pushGuard ⟨186,166,206,206,.south,19,19,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push244_1 : PushBound ⟨186,166,206,206,.south,19,19,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push244_1]; exact allowed)
  have checked := c22449 pattern guarded
  change d1267 pattern ≤ (19 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push244_2 (pattern : Twelve) : pushGuard ⟨186,166,206,206,.south,19,19,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push244_2 : PushBound ⟨186,166,206,206,.south,19,19,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push244_2]; exact allowed)
  have checked := c22552 pattern guarded
  change d1636 pattern ≤ (19 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push244_3 (pattern : Twelve) : pushGuard ⟨186,166,206,206,.south,19,19,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push244_3 : PushBound ⟨186,166,206,206,.south,19,19,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push244_3]; exact allowed)
  have checked := c22606 pattern guarded
  change d1827 pattern ≤ (19 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push245_0 (pattern : Twelve) : pushGuard ⟨186,187,185,185,.west,2,19,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push245_0 : PushBound ⟨186,187,185,185,.west,2,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push245_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push245_1 (pattern : Twelve) : pushGuard ⟨186,187,185,185,.west,2,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push245_1 : PushBound ⟨186,187,185,185,.west,2,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push245_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
end NetHack.Sokoban21
