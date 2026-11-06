/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers55
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push58_0 (pattern : Twelve) : pushGuard ⟨62,82,42,42,.north,2,9,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push58_0 : PushBound ⟨62,82,42,42,.north,2,9,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push58_1 (pattern : Twelve) : pushGuard ⟨62,82,42,42,.north,2,9,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push58_1 : PushBound ⟨62,82,42,42,.north,2,9,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push58_2 (pattern : Twelve) : pushGuard ⟨62,82,42,42,.north,2,9,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push58_2 : PushBound ⟨62,82,42,42,.north,2,9,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push58_3 (pattern : Twelve) : pushGuard ⟨62,82,42,42,.north,2,9,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push58_3 : PushBound ⟨62,82,42,42,.north,2,9,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push59_0 (pattern : Twelve) : pushGuard ⟨62,42,82,82,.south,0,9,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push59_0 : PushBound ⟨62,42,82,82,.south,0,9,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push59_1 (pattern : Twelve) : pushGuard ⟨62,42,82,82,.south,0,9,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push59_1 : PushBound ⟨62,42,82,82,.south,0,9,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push59_2 (pattern : Twelve) : pushGuard ⟨62,42,82,82,.south,0,9,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push59_2 : PushBound ⟨62,42,82,82,.south,0,9,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push59_3 (pattern : Twelve) : pushGuard ⟨62,42,82,82,.south,0,9,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push59_3 : PushBound ⟨62,42,82,82,.south,0,9,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push60_0 (pattern : Twelve) : pushGuard ⟨64,84,44,44,.north,0,5,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push60_0 : PushBound ⟨64,84,44,44,.north,0,5,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push60_1 (pattern : Twelve) : pushGuard ⟨64,84,44,44,.north,0,5,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push60_1 : PushBound ⟨64,84,44,44,.north,0,5,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push60_2 (pattern : Twelve) : pushGuard ⟨64,84,44,44,.north,0,5,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push60_2 : PushBound ⟨64,84,44,44,.north,0,5,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push60_3 (pattern : Twelve) : pushGuard ⟨64,84,44,44,.north,0,5,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push60_3 : PushBound ⟨64,84,44,44,.north,0,5,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push61_0 (pattern : Twelve) : pushGuard ⟨64,44,84,84,.south,5,5,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push61_0 : PushBound ⟨64,44,84,84,.south,5,5,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_0]; exact allowed)
  have checked := c13109 pattern guarded
  change d116 pattern ≤ (5 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push61_1 (pattern : Twelve) : pushGuard ⟨64,44,84,84,.south,5,5,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push61_1 : PushBound ⟨64,44,84,84,.south,5,5,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_1]; exact allowed)
  have checked := c13194 pattern guarded
  change d871 pattern ≤ (5 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push61_2 (pattern : Twelve) : pushGuard ⟨64,44,84,84,.south,5,5,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push61_2 : PushBound ⟨64,44,84,84,.south,5,5,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_2]; exact allowed)
  have checked := c13251 pattern guarded
  change d1323 pattern ≤ (5 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push61_3 (pattern : Twelve) : pushGuard ⟨64,44,84,84,.south,5,5,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push61_3 : PushBound ⟨64,44,84,84,.south,5,5,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_3]; exact allowed)
  have checked := c13278 pattern guarded
  change d1664 pattern ≤ (5 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push62_0 (pattern : Twelve) : pushGuard ⟨65,85,45,45,.north,2,4,false,false⟩ 0 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push62_0 : PushBound ⟨65,85,45,45,.north,2,4,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_0]; exact allowed)
  have checked := c13351 pattern guarded
  change d116 pattern ≤ (2 : Int) + d351 (change pattern 2 3)
  rw [s1950]
  exact checked
theorem guard_push62_1 (pattern : Twelve) : pushGuard ⟨65,85,45,45,.north,2,4,false,false⟩ 1 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push62_1 : PushBound ⟨65,85,45,45,.north,2,4,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_1]; exact allowed)
  have checked := c13407 pattern guarded
  change d871 pattern ≤ (2 : Int) + d1017 (change pattern 2 3)
  rw [s1987]
  exact checked
theorem guard_push62_2 (pattern : Twelve) : pushGuard ⟨65,85,45,45,.north,2,4,false,false⟩ 2 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push62_2 : PushBound ⟨65,85,45,45,.north,2,4,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_2]; exact allowed)
  have checked := c13452 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1434 (change pattern 2 3)
  rw [s2019]
  exact checked
theorem guard_push62_3 (pattern : Twelve) : pushGuard ⟨65,85,45,45,.north,2,4,false,false⟩ 3 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push62_3 : PushBound ⟨65,85,45,45,.north,2,4,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_3]; exact allowed)
  have checked := c13477 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1714 (change pattern 2 3)
  rw [s2037]
  exact checked
theorem guard_push63_0 (pattern : Twelve) : pushGuard ⟨65,64,66,66,.east,2,4,false,false⟩ 0 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push63_0 : PushBound ⟨65,64,66,66,.east,2,4,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_0]; exact allowed)
  have checked := c13530 pattern guarded
  change d116 pattern ≤ (2 : Int) + d351 (change pattern 2 9)
  rw [s2106]
  exact checked
theorem guard_push63_1 (pattern : Twelve) : pushGuard ⟨65,64,66,66,.east,2,4,false,false⟩ 1 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push63_1 : PushBound ⟨65,64,66,66,.east,2,4,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_1]; exact allowed)
  have checked := c13565 pattern guarded
  change d871 pattern ≤ (2 : Int) + d1017 (change pattern 2 9)
  rw [s2132]
  exact checked
theorem guard_push63_2 (pattern : Twelve) : pushGuard ⟨65,64,66,66,.east,2,4,false,false⟩ 2 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push63_2 : PushBound ⟨65,64,66,66,.east,2,4,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_2]; exact allowed)
  have checked := c13604 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1434 (change pattern 2 9)
  rw [s2156]
  exact checked
theorem guard_push63_3 (pattern : Twelve) : pushGuard ⟨65,64,66,66,.east,2,4,false,false⟩ 3 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push63_3 : PushBound ⟨65,64,66,66,.east,2,4,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_3]; exact allowed)
  have checked := c13625 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1714 (change pattern 2 9)
  rw [s2167]
  exact checked
theorem guard_push64_0 (pattern : Twelve) : pushGuard ⟨65,45,85,85,.south,4,4,false,true⟩ 0 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push64_0 : PushBound ⟨65,45,85,85,.south,4,4,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_0]; exact allowed)
  have checked := c13729 pattern guarded
  change d234 pattern ≤ (4 : Int) + d1017 (change pattern 2 12)
  rw [s2224]
  exact checked
theorem guard_push64_1 (pattern : Twelve) : pushGuard ⟨65,45,85,85,.south,4,4,false,true⟩ 1 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push64_1 : PushBound ⟨65,45,85,85,.south,4,4,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_1]; exact allowed)
  have checked := c13801 pattern guarded
  change d939 pattern ≤ (4 : Int) + d1434 (change pattern 2 12)
  rw [s2258]
  exact checked
theorem guard_push64_2 (pattern : Twelve) : pushGuard ⟨65,45,85,85,.south,4,4,false,true⟩ 2 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push64_2 : PushBound ⟨65,45,85,85,.south,4,4,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_2]; exact allowed)
  have checked := c13846 pattern guarded
  change d1379 pattern ≤ (4 : Int) + d1714 (change pattern 2 12)
  rw [s2276]
  exact checked
theorem guard_push64_3 (pattern : Twelve) : pushGuard ⟨65,45,85,85,.south,4,4,false,true⟩ 3 pattern = decide (d2266 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push64_3 : PushBound ⟨65,45,85,85,.south,4,4,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d2266 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_3]; exact allowed)
  have checked := c13856 pattern guarded
  change d1688 pattern ≤ (4 : Int) + d6 (change pattern 2 12)
  rw [s2188]
  exact checked
theorem guard_push65_0 (pattern : Twelve) : pushGuard ⟨65,66,64,64,.west,0,4,false,false⟩ 0 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push65_0 : PushBound ⟨65,66,64,64,.west,0,4,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_0]; exact allowed)
  have checked := c13869 pattern guarded
  change d365 pattern ≤ (0 : Int) + d351 (change pattern 2 12)
  rw [s2329]
  exact checked
theorem guard_push65_1 (pattern : Twelve) : pushGuard ⟨65,66,64,64,.west,0,4,false,false⟩ 1 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push65_1 : PushBound ⟨65,66,64,64,.west,0,4,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_1]; exact allowed)
  have checked := c13882 pattern guarded
  change d1029 pattern ≤ (0 : Int) + d1017 (change pattern 2 12)
  rw [s2224]
  exact checked
theorem guard_push65_2 (pattern : Twelve) : pushGuard ⟨65,66,64,64,.west,0,4,false,false⟩ 2 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push65_2 : PushBound ⟨65,66,64,64,.west,0,4,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_2]; exact allowed)
  have checked := c13892 pattern guarded
  change d1443 pattern ≤ (0 : Int) + d1434 (change pattern 2 12)
  rw [s2258]
  exact checked
theorem guard_push65_3 (pattern : Twelve) : pushGuard ⟨65,66,64,64,.west,0,4,false,false⟩ 3 pattern = decide (d2270 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases j <;> rfl
theorem push65_3 : PushBound ⟨65,66,64,64,.west,0,4,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2270 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_3]; exact allowed)
  have checked := c13894 pattern guarded
  change d1715 pattern ≤ (0 : Int) + d1714 (change pattern 2 12)
  rw [s2276]
  exact checked
theorem guard_push66_0 (pattern : Twelve) : pushGuard ⟨66,65,67,67,.east,2,3,false,false⟩ 0 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push66_0 : PushBound ⟨66,65,67,67,.east,2,3,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_0]; exact allowed)
  have checked := c13980 pattern guarded
  change d351 pattern ≤ (2 : Int) + d365 (change pattern 9 8)
  rw [s2368]
  exact checked
theorem guard_push66_1 (pattern : Twelve) : pushGuard ⟨66,65,67,67,.east,2,3,false,false⟩ 1 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push66_1 : PushBound ⟨66,65,67,67,.east,2,3,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_1]; exact allowed)
  have checked := c14024 pattern guarded
  change d1017 pattern ≤ (2 : Int) + d1029 (change pattern 9 8)
  rw [s2398]
  exact checked
theorem guard_push66_2 (pattern : Twelve) : pushGuard ⟨66,65,67,67,.east,2,3,false,false⟩ 2 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push66_2 : PushBound ⟨66,65,67,67,.east,2,3,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_2]; exact allowed)
  have checked := c14064 pattern guarded
  change d1434 pattern ≤ (2 : Int) + d1443 (change pattern 9 8)
  rw [s2419]
  exact checked
theorem guard_push66_3 (pattern : Twelve) : pushGuard ⟨66,65,67,67,.east,2,3,false,false⟩ 3 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push66_3 : PushBound ⟨66,65,67,67,.east,2,3,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_3]; exact allowed)
  have checked := c14081 pattern guarded
  change d1714 pattern ≤ (2 : Int) + d1715 (change pattern 9 8)
  rw [s2424]
  exact checked
theorem guard_push67_0 (pattern : Twelve) : pushGuard ⟨66,67,65,65,.west,0,3,false,false⟩ 0 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push67_0 : PushBound ⟨66,67,65,65,.west,0,3,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_0]; exact allowed)
  have checked := c14115 pattern guarded
  change d424 pattern ≤ (0 : Int) + d365 (change pattern 9 2)
  rw [s2465]
  exact checked
theorem guard_push67_1 (pattern : Twelve) : pushGuard ⟨66,67,65,65,.west,0,3,false,false⟩ 1 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push67_1 : PushBound ⟨66,67,65,65,.west,0,3,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_1]; exact allowed)
  have checked := c14139 pattern guarded
  change d1069 pattern ≤ (0 : Int) + d1029 (change pattern 9 2)
  rw [s2491]
  exact checked
theorem guard_push67_2 (pattern : Twelve) : pushGuard ⟨66,67,65,65,.west,0,3,false,false⟩ 2 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push67_2 : PushBound ⟨66,67,65,65,.west,0,3,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_2]; exact allowed)
  have checked := c14160 pattern guarded
  change d1471 pattern ≤ (0 : Int) + d1443 (change pattern 9 2)
  rw [s2508]
  exact checked
theorem guard_push67_3 (pattern : Twelve) : pushGuard ⟨66,67,65,65,.west,0,3,false,false⟩ 3 pattern = decide (d2280 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases i <;> cases j <;> rfl
theorem push67_3 : PushBound ⟨66,67,65,65,.west,0,3,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2280 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_3]; exact allowed)
  have checked := c14167 pattern guarded
  change d1729 pattern ≤ (0 : Int) + d1715 (change pattern 9 2)
  rw [s2513]
  exact checked
theorem guard_push68_0 (pattern : Twelve) : pushGuard ⟨67,87,47,47,.north,2,2,false,false⟩ 0 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push68_0 : PushBound ⟨67,87,47,47,.north,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_0]; exact allowed)
  have checked := c14283 pattern guarded
  change d156 pattern ≤ (2 : Int) + d424 (change pattern 8 7)
  rw [s2602]
  exact checked
theorem guard_push68_1 (pattern : Twelve) : pushGuard ⟨67,87,47,47,.north,2,2,false,false⟩ 1 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push68_1 : PushBound ⟨67,87,47,47,.north,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_1]; exact allowed)
  have checked := c14375 pattern guarded
  change d907 pattern ≤ (2 : Int) + d1069 (change pattern 8 7)
  rw [s2653]
  exact checked
theorem guard_push68_2 (pattern : Twelve) : pushGuard ⟨67,87,47,47,.north,2,2,false,false⟩ 2 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push68_2 : PushBound ⟨67,87,47,47,.north,2,2,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_2]; exact allowed)
  have checked := c14448 pattern guarded
  change d1354 pattern ≤ (2 : Int) + d1471 (change pattern 8 7)
  rw [s2686]
  exact checked
theorem guard_push68_3 (pattern : Twelve) : pushGuard ⟨67,87,47,47,.north,2,2,false,false⟩ 3 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push68_3 : PushBound ⟨67,87,47,47,.north,2,2,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_3]; exact allowed)
  have checked := c14500 pattern guarded
  change d1678 pattern ≤ (2 : Int) + d1729 (change pattern 8 7)
  rw [s2708]
  exact checked
theorem guard_push69_0 (pattern : Twelve) : pushGuard ⟨67,66,68,68,.east,2,2,false,false⟩ 0 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push69_0 : PushBound ⟨67,66,68,68,.east,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_0]; exact allowed)
  have checked := c14561 pattern guarded
  change d365 pattern ≤ (2 : Int) + d424 (change pattern 8 5)
  rw [s2787]
  exact checked
theorem guard_push69_1 (pattern : Twelve) : pushGuard ⟨67,66,68,68,.east,2,2,false,false⟩ 1 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push69_1 : PushBound ⟨67,66,68,68,.east,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_1]; exact allowed)
  have checked := c14621 pattern guarded
  change d1029 pattern ≤ (2 : Int) + d1069 (change pattern 8 5)
  rw [s2836]
  exact checked
theorem guard_push69_2 (pattern : Twelve) : pushGuard ⟨67,66,68,68,.east,2,2,false,false⟩ 2 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push69_2 : PushBound ⟨67,66,68,68,.east,2,2,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_2]; exact allowed)
  have checked := c14666 pattern guarded
  change d1443 pattern ≤ (2 : Int) + d1471 (change pattern 8 5)
  rw [s2872]
  exact checked
theorem guard_push69_3 (pattern : Twelve) : pushGuard ⟨67,66,68,68,.east,2,2,false,false⟩ 3 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push69_3 : PushBound ⟨67,66,68,68,.east,2,2,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_3]; exact allowed)
  have checked := c14687 pattern guarded
  change d1715 pattern ≤ (2 : Int) + d1729 (change pattern 8 5)
  rw [s2893]
  exact checked
theorem guard_push70_0 (pattern : Twelve) : pushGuard ⟨67,47,87,87,.south,2,2,false,false⟩ 0 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push70_0 : PushBound ⟨67,47,87,87,.south,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_0]; exact allowed)
  have checked := c14793 pattern guarded
  change d303 pattern ≤ (2 : Int) + d424 (change pattern 8 12)
  rw [s2986]
  exact checked
theorem guard_push70_1 (pattern : Twelve) : pushGuard ⟨67,47,87,87,.south,2,2,false,false⟩ 1 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push70_1 : PushBound ⟨67,47,87,87,.south,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_1]; exact allowed)
  have checked := c14861 pattern guarded
  change d979 pattern ≤ (2 : Int) + d1069 (change pattern 8 12)
  rw [s3037]
  exact checked
end NetHack.Sokoban21
