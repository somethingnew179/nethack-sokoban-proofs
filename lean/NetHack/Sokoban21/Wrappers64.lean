/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers63
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push158_0 (pattern : Twelve) : pushGuard ⟨122,142,102,102,.north,2,12,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push158_0 : PushBound ⟨122,142,102,102,.north,2,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push158_1 (pattern : Twelve) : pushGuard ⟨122,142,102,102,.north,2,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push158_1 : PushBound ⟨122,142,102,102,.north,2,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push158_2 (pattern : Twelve) : pushGuard ⟨122,142,102,102,.north,2,12,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push158_2 : PushBound ⟨122,142,102,102,.north,2,12,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push158_3 (pattern : Twelve) : pushGuard ⟨122,142,102,102,.north,2,12,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push158_3 : PushBound ⟨122,142,102,102,.north,2,12,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push159_0 (pattern : Twelve) : pushGuard ⟨122,121,123,123,.east,0,12,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push159_0 : PushBound ⟨122,121,123,123,.east,0,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push159_1 (pattern : Twelve) : pushGuard ⟨122,121,123,123,.east,0,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push159_1 : PushBound ⟨122,121,123,123,.east,0,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push159_2 (pattern : Twelve) : pushGuard ⟨122,121,123,123,.east,0,12,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push159_2 : PushBound ⟨122,121,123,123,.east,0,12,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push159_3 (pattern : Twelve) : pushGuard ⟨122,121,123,123,.east,0,12,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push159_3 : PushBound ⟨122,121,123,123,.east,0,12,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push160_0 (pattern : Twelve) : pushGuard ⟨122,102,142,142,.south,0,12,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push160_0 : PushBound ⟨122,102,142,142,.south,0,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push160_1 (pattern : Twelve) : pushGuard ⟨122,102,142,142,.south,0,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push160_1 : PushBound ⟨122,102,142,142,.south,0,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push160_2 (pattern : Twelve) : pushGuard ⟨122,102,142,142,.south,0,12,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push160_2 : PushBound ⟨122,102,142,142,.south,0,12,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push160_3 (pattern : Twelve) : pushGuard ⟨122,102,142,142,.south,0,12,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push160_3 : PushBound ⟨122,102,142,142,.south,0,12,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push161_0 (pattern : Twelve) : pushGuard ⟨122,123,121,121,.west,12,12,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push161_0 : PushBound ⟨122,123,121,121,.west,12,12,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_0]; exact allowed)
  have checked := c18949 pattern guarded
  change d116 pattern ≤ (12 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push161_1 (pattern : Twelve) : pushGuard ⟨122,123,121,121,.west,12,12,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push161_1 : PushBound ⟨122,123,121,121,.west,12,12,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_1]; exact allowed)
  have checked := c19034 pattern guarded
  change d871 pattern ≤ (12 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push161_2 (pattern : Twelve) : pushGuard ⟨122,123,121,121,.west,12,12,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push161_2 : PushBound ⟨122,123,121,121,.west,12,12,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_2]; exact allowed)
  have checked := c19091 pattern guarded
  change d1323 pattern ≤ (12 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push161_3 (pattern : Twelve) : pushGuard ⟨122,123,121,121,.west,12,12,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push161_3 : PushBound ⟨122,123,121,121,.west,12,12,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_3]; exact allowed)
  have checked := c19118 pattern guarded
  change d1664 pattern ≤ (12 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push162_0 (pattern : Twelve) : pushGuard ⟨123,143,103,103,.north,13,13,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push162_0 : PushBound ⟨123,143,103,103,.north,13,13,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_0]; exact allowed)
  have checked := c19267 pattern guarded
  change d116 pattern ≤ (13 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push162_1 (pattern : Twelve) : pushGuard ⟨123,143,103,103,.north,13,13,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push162_1 : PushBound ⟨123,143,103,103,.north,13,13,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_1]; exact allowed)
  have checked := c19352 pattern guarded
  change d871 pattern ≤ (13 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push162_2 (pattern : Twelve) : pushGuard ⟨123,143,103,103,.north,13,13,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push162_2 : PushBound ⟨123,143,103,103,.north,13,13,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_2]; exact allowed)
  have checked := c19409 pattern guarded
  change d1323 pattern ≤ (13 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push162_3 (pattern : Twelve) : pushGuard ⟨123,143,103,103,.north,13,13,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push162_3 : PushBound ⟨123,143,103,103,.north,13,13,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_3]; exact allowed)
  have checked := c19436 pattern guarded
  change d1664 pattern ≤ (13 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push163_0 (pattern : Twelve) : pushGuard ⟨123,103,143,143,.south,0,13,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push163_0 : PushBound ⟨123,103,143,143,.south,0,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push163_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push163_1 (pattern : Twelve) : pushGuard ⟨123,103,143,143,.south,0,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push163_1 : PushBound ⟨123,103,143,143,.south,0,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push163_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push163_2 (pattern : Twelve) : pushGuard ⟨123,103,143,143,.south,0,13,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push163_2 : PushBound ⟨123,103,143,143,.south,0,13,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push163_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push163_3 (pattern : Twelve) : pushGuard ⟨123,103,143,143,.south,0,13,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push163_3 : PushBound ⟨123,103,143,143,.south,0,13,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push163_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push164_0 (pattern : Twelve) : pushGuard ⟨126,146,106,106,.north,16,16,false,true⟩ 0 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push164_0 : PushBound ⟨126,146,106,106,.north,16,16,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push164_0]; exact allowed)
  have checked := c19642 pattern guarded
  change d806 pattern ≤ (16 : Int) + d1270 (change pattern 6 12)
  rw [s5261]
  exact checked
theorem guard_push164_1 (pattern : Twelve) : pushGuard ⟨126,146,106,106,.north,16,16,false,true⟩ 1 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push164_1 : PushBound ⟨126,146,106,106,.north,16,16,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push164_1]; exact allowed)
  have checked := c19776 pattern guarded
  change d1267 pattern ≤ (16 : Int) + d1639 (change pattern 6 12)
  rw [s5328]
  exact checked
theorem guard_push164_2 (pattern : Twelve) : pushGuard ⟨126,146,106,106,.north,16,16,false,true⟩ 2 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push164_2 : PushBound ⟨126,146,106,106,.north,16,16,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push164_2]; exact allowed)
  have checked := c19871 pattern guarded
  change d1636 pattern ≤ (16 : Int) + d1830 (change pattern 6 12)
  rw [s5368]
  exact checked
theorem guard_push164_3 (pattern : Twelve) : pushGuard ⟨126,146,106,106,.north,16,16,false,true⟩ 3 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push164_3 : PushBound ⟨126,146,106,106,.north,16,16,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push164_3]; exact allowed)
  have checked := c19916 pattern guarded
  change d1827 pattern ≤ (16 : Int) + d6 (change pattern 6 12)
  rw [s5169]
  exact checked
theorem guard_push165_0 (pattern : Twelve) : pushGuard ⟨126,125,127,127,.east,16,16,false,true⟩ 0 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push165_0 : PushBound ⟨126,125,127,127,.east,16,16,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push165_0]; exact allowed)
  have checked := c19642 pattern guarded
  change d806 pattern ≤ (16 : Int) + d1270 (change pattern 6 12)
  rw [s5261]
  exact checked
theorem guard_push165_1 (pattern : Twelve) : pushGuard ⟨126,125,127,127,.east,16,16,false,true⟩ 1 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push165_1 : PushBound ⟨126,125,127,127,.east,16,16,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push165_1]; exact allowed)
  have checked := c19776 pattern guarded
  change d1267 pattern ≤ (16 : Int) + d1639 (change pattern 6 12)
  rw [s5328]
  exact checked
theorem guard_push165_2 (pattern : Twelve) : pushGuard ⟨126,125,127,127,.east,16,16,false,true⟩ 2 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push165_2 : PushBound ⟨126,125,127,127,.east,16,16,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push165_2]; exact allowed)
  have checked := c19871 pattern guarded
  change d1636 pattern ≤ (16 : Int) + d1830 (change pattern 6 12)
  rw [s5368]
  exact checked
theorem guard_push165_3 (pattern : Twelve) : pushGuard ⟨126,125,127,127,.east,16,16,false,true⟩ 3 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push165_3 : PushBound ⟨126,125,127,127,.east,16,16,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push165_3]; exact allowed)
  have checked := c19916 pattern guarded
  change d1827 pattern ≤ (16 : Int) + d6 (change pattern 6 12)
  rw [s5169]
  exact checked
theorem guard_push166_0 (pattern : Twelve) : pushGuard ⟨126,106,146,146,.south,0,16,false,false⟩ 0 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push166_0 : PushBound ⟨126,106,146,146,.south,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push166_0]; exact allowed)
  have checked := c19917 pattern guarded
  change d156 pattern ≤ (0 : Int) + d809 (change pattern 6 12)
  rw [s5446]
  exact checked
theorem guard_push166_1 (pattern : Twelve) : pushGuard ⟨126,106,146,146,.south,0,16,false,false⟩ 1 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push166_1 : PushBound ⟨126,106,146,146,.south,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push166_1]; exact allowed)
  have checked := c19918 pattern guarded
  change d907 pattern ≤ (0 : Int) + d1270 (change pattern 6 12)
  rw [s5261]
  exact checked
theorem guard_push166_2 (pattern : Twelve) : pushGuard ⟨126,106,146,146,.south,0,16,false,false⟩ 2 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push166_2 : PushBound ⟨126,106,146,146,.south,0,16,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push166_2]; exact allowed)
  have checked := c19919 pattern guarded
  change d1354 pattern ≤ (0 : Int) + d1639 (change pattern 6 12)
  rw [s5328]
  exact checked
theorem guard_push166_3 (pattern : Twelve) : pushGuard ⟨126,106,146,146,.south,0,16,false,false⟩ 3 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push166_3 : PushBound ⟨126,106,146,146,.south,0,16,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push166_3]; exact allowed)
  have checked := c19920 pattern guarded
  change d1678 pattern ≤ (0 : Int) + d1830 (change pattern 6 12)
  rw [s5368]
  exact checked
theorem guard_push167_0 (pattern : Twelve) : pushGuard ⟨126,127,125,125,.west,16,16,false,true⟩ 0 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push167_0 : PushBound ⟨126,127,125,125,.west,16,16,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push167_0]; exact allowed)
  have checked := c20005 pattern guarded
  change d156 pattern ≤ (16 : Int) + d1270 (change pattern 6 12)
  rw [s5261]
  exact checked
theorem guard_push167_1 (pattern : Twelve) : pushGuard ⟨126,127,125,125,.west,16,16,false,true⟩ 1 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push167_1 : PushBound ⟨126,127,125,125,.west,16,16,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push167_1]; exact allowed)
  have checked := c20066 pattern guarded
  change d907 pattern ≤ (16 : Int) + d1639 (change pattern 6 12)
  rw [s5328]
  exact checked
theorem guard_push167_2 (pattern : Twelve) : pushGuard ⟨126,127,125,125,.west,16,16,false,true⟩ 2 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push167_2 : PushBound ⟨126,127,125,125,.west,16,16,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push167_2]; exact allowed)
  have checked := c20114 pattern guarded
  change d1354 pattern ≤ (16 : Int) + d1830 (change pattern 6 12)
  rw [s5368]
  exact checked
theorem guard_push167_3 (pattern : Twelve) : pushGuard ⟨126,127,125,125,.west,16,16,false,true⟩ 3 pattern = decide (d1872 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push167_3 : PushBound ⟨126,127,125,125,.west,16,16,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1872 pattern = 1 := of_decide_eq_true (by rw [← guard_push167_3]; exact allowed)
  have checked := c20130 pattern guarded
  change d1678 pattern ≤ (16 : Int) + d6 (change pattern 6 12)
  rw [s5169]
  exact checked
theorem guard_push168_0 (pattern : Twelve) : pushGuard ⟨129,149,109,109,.north,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push168_0 : PushBound ⟨129,149,109,109,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push168_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push168_1 (pattern : Twelve) : pushGuard ⟨129,149,109,109,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push168_1 : PushBound ⟨129,149,109,109,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push168_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push168_2 (pattern : Twelve) : pushGuard ⟨129,149,109,109,.north,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push168_2 : PushBound ⟨129,149,109,109,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push168_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push168_3 (pattern : Twelve) : pushGuard ⟨129,149,109,109,.north,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push168_3 : PushBound ⟨129,149,109,109,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push168_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push169_0 (pattern : Twelve) : pushGuard ⟨129,109,149,149,.south,1,1,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push169_0 : PushBound ⟨129,109,149,149,.south,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push169_0]; exact allowed)
  have checked := c18628 pattern guarded
  change d156 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push169_1 (pattern : Twelve) : pushGuard ⟨129,109,149,149,.south,1,1,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push169_1 : PushBound ⟨129,109,149,149,.south,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push169_1]; exact allowed)
  have checked := c18699 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push169_2 (pattern : Twelve) : pushGuard ⟨129,109,149,149,.south,1,1,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push169_2 : PushBound ⟨129,109,149,149,.south,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push169_2]; exact allowed)
  have checked := c18763 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push169_3 (pattern : Twelve) : pushGuard ⟨129,109,149,149,.south,1,1,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push169_3 : PushBound ⟨129,109,149,149,.south,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push169_3]; exact allowed)
  have checked := c18800 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push170_0 (pattern : Twelve) : pushGuard ⟨130,150,110,110,.north,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push170_0 : PushBound ⟨130,150,110,110,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push170_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push170_1 (pattern : Twelve) : pushGuard ⟨130,150,110,110,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push170_1 : PushBound ⟨130,150,110,110,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push170_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
end NetHack.Sokoban21
