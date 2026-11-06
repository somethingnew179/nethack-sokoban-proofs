/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers67
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push208_0 (pattern : Twelve) : pushGuard ⟨162,182,142,142,.north,2,14,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push208_0 : PushBound ⟨162,182,142,142,.north,2,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push208_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push208_1 (pattern : Twelve) : pushGuard ⟨162,182,142,142,.north,2,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push208_1 : PushBound ⟨162,182,142,142,.north,2,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push208_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push208_2 (pattern : Twelve) : pushGuard ⟨162,182,142,142,.north,2,14,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push208_2 : PushBound ⟨162,182,142,142,.north,2,14,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push208_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push208_3 (pattern : Twelve) : pushGuard ⟨162,182,142,142,.north,2,14,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push208_3 : PushBound ⟨162,182,142,142,.north,2,14,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push208_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push209_0 (pattern : Twelve) : pushGuard ⟨162,142,182,182,.south,0,14,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push209_0 : PushBound ⟨162,142,182,182,.south,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push209_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push209_1 (pattern : Twelve) : pushGuard ⟨162,142,182,182,.south,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push209_1 : PushBound ⟨162,142,182,182,.south,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push209_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push209_2 (pattern : Twelve) : pushGuard ⟨162,142,182,182,.south,0,14,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push209_2 : PushBound ⟨162,142,182,182,.south,0,14,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push209_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push209_3 (pattern : Twelve) : pushGuard ⟨162,142,182,182,.south,0,14,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push209_3 : PushBound ⟨162,142,182,182,.south,0,14,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push209_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push210_0 (pattern : Twelve) : pushGuard ⟨163,183,143,143,.north,2,15,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push210_0 : PushBound ⟨163,183,143,143,.north,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push210_0]; exact allowed)
  have checked := c20626 pattern guarded
  change d813 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push210_1 (pattern : Twelve) : pushGuard ⟨163,183,143,143,.north,2,15,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push210_1 : PushBound ⟨163,183,143,143,.north,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push210_1]; exact allowed)
  have checked := c20628 pattern guarded
  change d1274 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push210_2 (pattern : Twelve) : pushGuard ⟨163,183,143,143,.north,2,15,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push210_2 : PushBound ⟨163,183,143,143,.north,2,15,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push210_2]; exact allowed)
  have checked := c20630 pattern guarded
  change d1643 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push210_3 (pattern : Twelve) : pushGuard ⟨163,183,143,143,.north,2,15,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push210_3 : PushBound ⟨163,183,143,143,.north,2,15,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push210_3]; exact allowed)
  have checked := c20632 pattern guarded
  change d1834 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push211_0 (pattern : Twelve) : pushGuard ⟨163,143,183,183,.south,0,15,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push211_0 : PushBound ⟨163,143,183,183,.south,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push211_0]; exact allowed)
  have checked := c20633 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 0)
  rw [s6377]
  exact checked
theorem guard_push211_1 (pattern : Twelve) : pushGuard ⟨163,143,183,183,.south,0,15,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push211_1 : PushBound ⟨163,143,183,183,.south,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push211_1]; exact allowed)
  have checked := c20634 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 0)
  rw [s6435]
  exact checked
theorem guard_push211_2 (pattern : Twelve) : pushGuard ⟨163,143,183,183,.south,0,15,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push211_2 : PushBound ⟨163,143,183,183,.south,0,15,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push211_2]; exact allowed)
  have checked := c20635 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 0)
  rw [s6488]
  exact checked
theorem guard_push211_3 (pattern : Twelve) : pushGuard ⟨163,143,183,183,.south,0,15,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push211_3 : PushBound ⟨163,143,183,183,.south,0,15,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push211_3]; exact allowed)
  have checked := c20636 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 0)
  rw [s6511]
  exact checked
theorem guard_push212_0 (pattern : Twelve) : pushGuard ⟨165,185,145,145,.north,2,17,false,false⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push212_0 : PushBound ⟨165,185,145,145,.north,2,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push212_0]; exact allowed)
  have checked := c20637 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 1)
  rw [s6696]
  exact checked
theorem guard_push212_1 (pattern : Twelve) : pushGuard ⟨165,185,145,145,.north,2,17,false,false⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push212_1 : PushBound ⟨165,185,145,145,.north,2,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push212_1]; exact allowed)
  have checked := c20638 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 1)
  rw [s6810]
  exact checked
theorem guard_push212_2 (pattern : Twelve) : pushGuard ⟨165,185,145,145,.north,2,17,false,false⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push212_2 : PushBound ⟨165,185,145,145,.north,2,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push212_2]; exact allowed)
  have checked := c20639 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 1)
  rw [s6911]
  exact checked
theorem guard_push212_3 (pattern : Twelve) : pushGuard ⟨165,185,145,145,.north,2,17,false,false⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push212_3 : PushBound ⟨165,185,145,145,.north,2,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push212_3]; exact allowed)
  have checked := c20640 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 1)
  rw [s6960]
  exact checked
theorem guard_push213_0 (pattern : Twelve) : pushGuard ⟨165,145,185,185,.south,0,17,false,false⟩ 0 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push213_0 : PushBound ⟨165,145,185,185,.south,0,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push213_0]; exact allowed)
  have checked := c9737 pattern guarded
  change d812 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push213_1 (pattern : Twelve) : pushGuard ⟨165,145,185,185,.south,0,17,false,false⟩ 1 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push213_1 : PushBound ⟨165,145,185,185,.south,0,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push213_1]; exact allowed)
  have checked := c9742 pattern guarded
  change d1273 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push213_2 (pattern : Twelve) : pushGuard ⟨165,145,185,185,.south,0,17,false,false⟩ 2 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push213_2 : PushBound ⟨165,145,185,185,.south,0,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push213_2]; exact allowed)
  have checked := c9747 pattern guarded
  change d1642 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push213_3 (pattern : Twelve) : pushGuard ⟨165,145,185,185,.south,0,17,false,false⟩ 3 pattern = decide (d1873 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push213_3 : PushBound ⟨165,145,185,185,.south,0,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1873 pattern = 1 := of_decide_eq_true (by rw [← guard_push213_3]; exact allowed)
  have checked := c9751 pattern guarded
  change d1833 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push214_0 (pattern : Twelve) : pushGuard ⟨166,186,146,146,.north,2,18,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push214_0 : PushBound ⟨166,186,146,146,.north,2,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push214_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push214_1 (pattern : Twelve) : pushGuard ⟨166,186,146,146,.north,2,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push214_1 : PushBound ⟨166,186,146,146,.north,2,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push214_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push214_2 (pattern : Twelve) : pushGuard ⟨166,186,146,146,.north,2,18,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push214_2 : PushBound ⟨166,186,146,146,.north,2,18,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push214_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push214_3 (pattern : Twelve) : pushGuard ⟨166,186,146,146,.north,2,18,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push214_3 : PushBound ⟨166,186,146,146,.north,2,18,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push214_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push215_0 (pattern : Twelve) : pushGuard ⟨166,146,186,186,.south,0,18,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push215_0 : PushBound ⟨166,146,186,186,.south,0,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push215_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push215_1 (pattern : Twelve) : pushGuard ⟨166,146,186,186,.south,0,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push215_1 : PushBound ⟨166,146,186,186,.south,0,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push215_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push215_2 (pattern : Twelve) : pushGuard ⟨166,146,186,186,.south,0,18,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push215_2 : PushBound ⟨166,146,186,186,.south,0,18,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push215_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push215_3 (pattern : Twelve) : pushGuard ⟨166,146,186,186,.south,0,18,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push215_3 : PushBound ⟨166,146,186,186,.south,0,18,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push215_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push216_0 (pattern : Twelve) : pushGuard ⟨182,202,162,162,.north,2,15,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push216_0 : PushBound ⟨182,202,162,162,.north,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push216_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push216_1 (pattern : Twelve) : pushGuard ⟨182,202,162,162,.north,2,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push216_1 : PushBound ⟨182,202,162,162,.north,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push216_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push216_2 (pattern : Twelve) : pushGuard ⟨182,202,162,162,.north,2,15,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push216_2 : PushBound ⟨182,202,162,162,.north,2,15,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push216_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push216_3 (pattern : Twelve) : pushGuard ⟨182,202,162,162,.north,2,15,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push216_3 : PushBound ⟨182,202,162,162,.north,2,15,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push216_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push217_0 (pattern : Twelve) : pushGuard ⟨182,181,183,183,.east,0,15,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push217_0 : PushBound ⟨182,181,183,183,.east,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push217_0]; exact allowed)
  have checked := c20633 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 0)
  rw [s6377]
  exact checked
theorem guard_push217_1 (pattern : Twelve) : pushGuard ⟨182,181,183,183,.east,0,15,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push217_1 : PushBound ⟨182,181,183,183,.east,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push217_1]; exact allowed)
  have checked := c20634 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 0)
  rw [s6435]
  exact checked
theorem guard_push217_2 (pattern : Twelve) : pushGuard ⟨182,181,183,183,.east,0,15,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push217_2 : PushBound ⟨182,181,183,183,.east,0,15,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push217_2]; exact allowed)
  have checked := c20635 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 0)
  rw [s6488]
  exact checked
theorem guard_push217_3 (pattern : Twelve) : pushGuard ⟨182,181,183,183,.east,0,15,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push217_3 : PushBound ⟨182,181,183,183,.east,0,15,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push217_3]; exact allowed)
  have checked := c20636 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 0)
  rw [s6511]
  exact checked
theorem guard_push218_0 (pattern : Twelve) : pushGuard ⟨182,162,202,202,.south,15,15,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push218_0 : PushBound ⟨182,162,202,202,.south,15,15,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push218_0]; exact allowed)
  have checked := c20793 pattern guarded
  change d116 pattern ≤ (15 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push218_1 (pattern : Twelve) : pushGuard ⟨182,162,202,202,.south,15,15,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push218_1 : PushBound ⟨182,162,202,202,.south,15,15,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push218_1]; exact allowed)
  have checked := c20878 pattern guarded
  change d871 pattern ≤ (15 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push218_2 (pattern : Twelve) : pushGuard ⟨182,162,202,202,.south,15,15,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push218_2 : PushBound ⟨182,162,202,202,.south,15,15,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push218_2]; exact allowed)
  have checked := c20935 pattern guarded
  change d1323 pattern ≤ (15 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push218_3 (pattern : Twelve) : pushGuard ⟨182,162,202,202,.south,15,15,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push218_3 : PushBound ⟨182,162,202,202,.south,15,15,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push218_3]; exact allowed)
  have checked := c20962 pattern guarded
  change d1664 pattern ≤ (15 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push219_0 (pattern : Twelve) : pushGuard ⟨182,183,181,181,.west,15,15,false,true⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push219_0 : PushBound ⟨182,183,181,181,.west,15,15,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push219_0]; exact allowed)
  have checked := c20964 pattern guarded
  change d813 pattern ≤ (15 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push219_1 (pattern : Twelve) : pushGuard ⟨182,183,181,181,.west,15,15,false,true⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push219_1 : PushBound ⟨182,183,181,181,.west,15,15,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push219_1]; exact allowed)
  have checked := c20966 pattern guarded
  change d1274 pattern ≤ (15 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push219_2 (pattern : Twelve) : pushGuard ⟨182,183,181,181,.west,15,15,false,true⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push219_2 : PushBound ⟨182,183,181,181,.west,15,15,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push219_2]; exact allowed)
  have checked := c20968 pattern guarded
  change d1643 pattern ≤ (15 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push219_3 (pattern : Twelve) : pushGuard ⟨182,183,181,181,.west,15,15,false,true⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push219_3 : PushBound ⟨182,183,181,181,.west,15,15,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push219_3]; exact allowed)
  have checked := c20970 pattern guarded
  change d1834 pattern ≤ (15 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push220_0 (pattern : Twelve) : pushGuard ⟨183,203,163,163,.north,2,16,false,false⟩ 0 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push220_0 : PushBound ⟨183,203,163,163,.north,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push220_0]; exact allowed)
  have checked := c20971 pattern guarded
  change d116 pattern ≤ (2 : Int) + d813 (change pattern 0 12)
  rw [s7078]
  exact checked
theorem guard_push220_1 (pattern : Twelve) : pushGuard ⟨183,203,163,163,.north,2,16,false,false⟩ 1 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push220_1 : PushBound ⟨183,203,163,163,.north,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push220_1]; exact allowed)
  have checked := c20972 pattern guarded
  change d871 pattern ≤ (2 : Int) + d1274 (change pattern 0 12)
  rw [s7137]
  exact checked
end NetHack.Sokoban21
