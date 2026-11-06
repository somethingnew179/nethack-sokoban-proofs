/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers60
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push120_2 (pattern : Twelve) : pushGuard ⟨98,118,78,78,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push120_2 : PushBound ⟨98,118,78,78,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push120_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push120_3 (pattern : Twelve) : pushGuard ⟨98,118,78,78,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push120_3 : PushBound ⟨98,118,78,78,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push120_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push121_0 : PushBound ⟨98,78,118,118,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push121_1 (pattern : Twelve) : pushGuard ⟨98,78,118,118,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push121_1 : PushBound ⟨98,78,118,118,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push121_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push121_2 (pattern : Twelve) : pushGuard ⟨98,78,118,118,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push121_2 : PushBound ⟨98,78,118,118,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push121_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push121_3 (pattern : Twelve) : pushGuard ⟨98,78,118,118,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push121_3 : PushBound ⟨98,78,118,118,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push121_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem guard_push122_0 (pattern : Twelve) : pushGuard ⟨102,122,82,82,.north,2,11,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push122_0 : PushBound ⟨102,122,82,82,.north,2,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push122_1 (pattern : Twelve) : pushGuard ⟨102,122,82,82,.north,2,11,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push122_1 : PushBound ⟨102,122,82,82,.north,2,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push122_2 (pattern : Twelve) : pushGuard ⟨102,122,82,82,.north,2,11,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push122_2 : PushBound ⟨102,122,82,82,.north,2,11,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push122_3 (pattern : Twelve) : pushGuard ⟨102,122,82,82,.north,2,11,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push122_3 : PushBound ⟨102,122,82,82,.north,2,11,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push123_0 (pattern : Twelve) : pushGuard ⟨102,101,103,103,.east,11,11,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push123_0 : PushBound ⟨102,101,103,103,.east,11,11,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_0]; exact allowed)
  have checked := c18366 pattern guarded
  change d116 pattern ≤ (11 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push123_1 (pattern : Twelve) : pushGuard ⟨102,101,103,103,.east,11,11,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push123_1 : PushBound ⟨102,101,103,103,.east,11,11,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_1]; exact allowed)
  have checked := c18451 pattern guarded
  change d871 pattern ≤ (11 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push123_2 (pattern : Twelve) : pushGuard ⟨102,101,103,103,.east,11,11,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push123_2 : PushBound ⟨102,101,103,103,.east,11,11,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_2]; exact allowed)
  have checked := c18508 pattern guarded
  change d1323 pattern ≤ (11 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push123_3 (pattern : Twelve) : pushGuard ⟨102,101,103,103,.east,11,11,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push123_3 : PushBound ⟨102,101,103,103,.east,11,11,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_3]; exact allowed)
  have checked := c18535 pattern guarded
  change d1664 pattern ≤ (11 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push124_0 (pattern : Twelve) : pushGuard ⟨102,82,122,122,.south,0,11,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push124_0 : PushBound ⟨102,82,122,122,.south,0,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push124_1 (pattern : Twelve) : pushGuard ⟨102,82,122,122,.south,0,11,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push124_1 : PushBound ⟨102,82,122,122,.south,0,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push124_2 (pattern : Twelve) : pushGuard ⟨102,82,122,122,.south,0,11,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push124_2 : PushBound ⟨102,82,122,122,.south,0,11,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push124_3 (pattern : Twelve) : pushGuard ⟨102,82,122,122,.south,0,11,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push124_3 : PushBound ⟨102,82,122,122,.south,0,11,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push125_0 (pattern : Twelve) : pushGuard ⟨102,103,101,101,.west,11,11,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push125_0 : PushBound ⟨102,103,101,101,.west,11,11,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_0]; exact allowed)
  have checked := c18366 pattern guarded
  change d116 pattern ≤ (11 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push125_1 (pattern : Twelve) : pushGuard ⟨102,103,101,101,.west,11,11,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push125_1 : PushBound ⟨102,103,101,101,.west,11,11,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_1]; exact allowed)
  have checked := c18451 pattern guarded
  change d871 pattern ≤ (11 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push125_2 (pattern : Twelve) : pushGuard ⟨102,103,101,101,.west,11,11,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push125_2 : PushBound ⟨102,103,101,101,.west,11,11,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_2]; exact allowed)
  have checked := c18508 pattern guarded
  change d1323 pattern ≤ (11 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push125_3 (pattern : Twelve) : pushGuard ⟨102,103,101,101,.west,11,11,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push125_3 : PushBound ⟨102,103,101,101,.west,11,11,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_3]; exact allowed)
  have checked := c18535 pattern guarded
  change d1664 pattern ≤ (11 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push126_0 (pattern : Twelve) : pushGuard ⟨107,127,87,87,.north,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push126_0 : PushBound ⟨107,127,87,87,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push126_1 (pattern : Twelve) : pushGuard ⟨107,127,87,87,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push126_1 : PushBound ⟨107,127,87,87,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push126_2 (pattern : Twelve) : pushGuard ⟨107,127,87,87,.north,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push126_2 : PushBound ⟨107,127,87,87,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push126_3 (pattern : Twelve) : pushGuard ⟨107,127,87,87,.north,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push126_3 : PushBound ⟨107,127,87,87,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push127_0 (pattern : Twelve) : pushGuard ⟨107,106,108,108,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push127_0 : PushBound ⟨107,106,108,108,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push127_1 (pattern : Twelve) : pushGuard ⟨107,106,108,108,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push127_1 : PushBound ⟨107,106,108,108,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push127_2 (pattern : Twelve) : pushGuard ⟨107,106,108,108,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push127_2 : PushBound ⟨107,106,108,108,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push127_3 (pattern : Twelve) : pushGuard ⟨107,106,108,108,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push127_3 : PushBound ⟨107,106,108,108,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push128_0 (pattern : Twelve) : pushGuard ⟨107,87,127,127,.south,1,1,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push128_0 : PushBound ⟨107,87,127,127,.south,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_0]; exact allowed)
  have checked := c18628 pattern guarded
  change d156 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push128_1 (pattern : Twelve) : pushGuard ⟨107,87,127,127,.south,1,1,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push128_1 : PushBound ⟨107,87,127,127,.south,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_1]; exact allowed)
  have checked := c18699 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push128_2 (pattern : Twelve) : pushGuard ⟨107,87,127,127,.south,1,1,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push128_2 : PushBound ⟨107,87,127,127,.south,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_2]; exact allowed)
  have checked := c18763 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push128_3 (pattern : Twelve) : pushGuard ⟨107,87,127,127,.south,1,1,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push128_3 : PushBound ⟨107,87,127,127,.south,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_3]; exact allowed)
  have checked := c18800 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push129_0 (pattern : Twelve) : pushGuard ⟨107,108,106,106,.west,1,1,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push129_0 : PushBound ⟨107,108,106,106,.west,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_0]; exact allowed)
  have checked := c18628 pattern guarded
  change d156 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push129_1 (pattern : Twelve) : pushGuard ⟨107,108,106,106,.west,1,1,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push129_1 : PushBound ⟨107,108,106,106,.west,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_1]; exact allowed)
  have checked := c18699 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push129_2 (pattern : Twelve) : pushGuard ⟨107,108,106,106,.west,1,1,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push129_2 : PushBound ⟨107,108,106,106,.west,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_2]; exact allowed)
  have checked := c18763 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push129_3 (pattern : Twelve) : pushGuard ⟨107,108,106,106,.west,1,1,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push129_3 : PushBound ⟨107,108,106,106,.west,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_3]; exact allowed)
  have checked := c18800 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push130_0 (pattern : Twelve) : pushGuard ⟨108,107,109,109,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push130_0 : PushBound ⟨108,107,109,109,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push130_1 (pattern : Twelve) : pushGuard ⟨108,107,109,109,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push130_1 : PushBound ⟨108,107,109,109,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push130_2 (pattern : Twelve) : pushGuard ⟨108,107,109,109,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push130_2 : PushBound ⟨108,107,109,109,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push130_3 (pattern : Twelve) : pushGuard ⟨108,107,109,109,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push130_3 : PushBound ⟨108,107,109,109,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push131_0 (pattern : Twelve) : pushGuard ⟨108,109,107,107,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push131_0 : PushBound ⟨108,109,107,107,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push131_1 (pattern : Twelve) : pushGuard ⟨108,109,107,107,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push131_1 : PushBound ⟨108,109,107,107,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push131_2 (pattern : Twelve) : pushGuard ⟨108,109,107,107,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push131_2 : PushBound ⟨108,109,107,107,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push131_3 (pattern : Twelve) : pushGuard ⟨108,109,107,107,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push131_3 : PushBound ⟨108,109,107,107,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push132_0 (pattern : Twelve) : pushGuard ⟨109,108,110,110,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push132_0 : PushBound ⟨109,108,110,110,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push132_1 (pattern : Twelve) : pushGuard ⟨109,108,110,110,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push132_1 : PushBound ⟨109,108,110,110,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push132_2 (pattern : Twelve) : pushGuard ⟨109,108,110,110,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push132_2 : PushBound ⟨109,108,110,110,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push132_3 (pattern : Twelve) : pushGuard ⟨109,108,110,110,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push132_3 : PushBound ⟨109,108,110,110,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
end NetHack.Sokoban21
