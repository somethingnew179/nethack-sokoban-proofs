/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers58
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push95_2 (pattern : Twelve) : pushGuard ⟨78,58,98,98,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push95_2 : PushBound ⟨78,58,98,98,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push95_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push95_3 (pattern : Twelve) : pushGuard ⟨78,58,98,98,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push95_3 : PushBound ⟨78,58,98,98,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push95_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem guard_push96_0 (pattern : Twelve) : pushGuard ⟨82,102,62,62,.north,2,10,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push96_0 : PushBound ⟨82,102,62,62,.north,2,10,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_0]; exact allowed)
  have checked := c10135 pattern guarded
  change d116 pattern ≤ (2 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push96_1 (pattern : Twelve) : pushGuard ⟨82,102,62,62,.north,2,10,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push96_1 : PushBound ⟨82,102,62,62,.north,2,10,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_1]; exact allowed)
  have checked := c10136 pattern guarded
  change d871 pattern ≤ (2 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push96_2 (pattern : Twelve) : pushGuard ⟨82,102,62,62,.north,2,10,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push96_2 : PushBound ⟨82,102,62,62,.north,2,10,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_2]; exact allowed)
  have checked := c10137 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push96_3 (pattern : Twelve) : pushGuard ⟨82,102,62,62,.north,2,10,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push96_3 : PushBound ⟨82,102,62,62,.north,2,10,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_3]; exact allowed)
  have checked := c10138 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push97_0 (pattern : Twelve) : pushGuard ⟨82,62,102,102,.south,0,10,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push97_0 : PushBound ⟨82,62,102,102,.south,0,10,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_0]; exact allowed)
  have checked := c0 pattern guarded
  change d116 pattern ≤ (0 : Int) + d116 (change pattern 12 12)
  rw [s407]
  exact checked
theorem guard_push97_1 (pattern : Twelve) : pushGuard ⟨82,62,102,102,.south,0,10,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push97_1 : PushBound ⟨82,62,102,102,.south,0,10,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_1]; exact allowed)
  have checked := c1 pattern guarded
  change d871 pattern ≤ (0 : Int) + d871 (change pattern 12 12)
  rw [s95]
  exact checked
theorem guard_push97_2 (pattern : Twelve) : pushGuard ⟨82,62,102,102,.south,0,10,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push97_2 : PushBound ⟨82,62,102,102,.south,0,10,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push97_3 (pattern : Twelve) : pushGuard ⟨82,62,102,102,.south,0,10,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push97_3 : PushBound ⟨82,62,102,102,.south,0,10,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push98_0 (pattern : Twelve) : pushGuard ⟨87,107,67,67,.north,0,1,false,false⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push98_0 : PushBound ⟨87,107,67,67,.north,0,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_0]; exact allowed)
  have checked := c16776 pattern guarded
  change d156 pattern ≤ (0 : Int) + d156 (change pattern 12 8)
  rw [s4676]
  exact checked
theorem guard_push98_1 (pattern : Twelve) : pushGuard ⟨87,107,67,67,.north,0,1,false,false⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push98_1 : PushBound ⟨87,107,67,67,.north,0,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_1]; exact allowed)
  have checked := c16860 pattern guarded
  change d907 pattern ≤ (0 : Int) + d907 (change pattern 12 8)
  rw [s4748]
  exact checked
theorem guard_push98_2 (pattern : Twelve) : pushGuard ⟨87,107,67,67,.north,0,1,false,false⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push98_2 : PushBound ⟨87,107,67,67,.north,0,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_2]; exact allowed)
  have checked := c16938 pattern guarded
  change d1354 pattern ≤ (0 : Int) + d1354 (change pattern 12 8)
  rw [s4812]
  exact checked
theorem guard_push98_3 (pattern : Twelve) : pushGuard ⟨87,107,67,67,.north,0,1,false,false⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push98_3 : PushBound ⟨87,107,67,67,.north,0,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_3]; exact allowed)
  have checked := c16975 pattern guarded
  change d1678 pattern ≤ (0 : Int) + d1678 (change pattern 12 8)
  rw [s4850]
  exact checked
theorem guard_push99_0 (pattern : Twelve) : pushGuard ⟨87,67,107,107,.south,1,1,false,false⟩ 0 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push99_0 : PushBound ⟨87,67,107,107,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_0]; exact allowed)
  have checked := c17118 pattern guarded
  change d424 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push99_1 (pattern : Twelve) : pushGuard ⟨87,67,107,107,.south,1,1,false,false⟩ 1 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push99_1 : PushBound ⟨87,67,107,107,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_1]; exact allowed)
  have checked := c17207 pattern guarded
  change d1069 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push99_2 (pattern : Twelve) : pushGuard ⟨87,67,107,107,.south,1,1,false,false⟩ 2 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push99_2 : PushBound ⟨87,67,107,107,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_2]; exact allowed)
  have checked := c17275 pattern guarded
  change d1471 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push99_3 (pattern : Twelve) : pushGuard ⟨87,67,107,107,.south,1,1,false,false⟩ 3 pattern = decide (d1848 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases i <;> rfl
theorem push99_3 : PushBound ⟨87,67,107,107,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1848 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_3]; exact allowed)
  have checked := c17315 pattern guarded
  change d1729 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push100_0 (pattern : Twelve) : pushGuard ⟨88,108,68,68,.north,1,1,false,false⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push100_0 : PushBound ⟨88,108,68,68,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push100_0]; exact allowed)
  have checked := c17432 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 5)
  rw [s4991]
  exact checked
theorem guard_push100_1 (pattern : Twelve) : pushGuard ⟨88,108,68,68,.north,1,1,false,false⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push100_1 : PushBound ⟨88,108,68,68,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push100_1]; exact allowed)
  have checked := c17541 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 5)
  rw [s5055]
  exact checked
theorem guard_push100_2 (pattern : Twelve) : pushGuard ⟨88,108,68,68,.north,1,1,false,false⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push100_2 : PushBound ⟨88,108,68,68,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push100_2]; exact allowed)
  have checked := c17620 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 5)
  rw [s5111]
  exact checked
theorem guard_push100_3 (pattern : Twelve) : pushGuard ⟨88,108,68,68,.north,1,1,false,false⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push100_3 : PushBound ⟨88,108,68,68,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push100_3]; exact allowed)
  have checked := c17669 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 5)
  rw [s5148]
  exact checked
theorem guard_push101_0 (pattern : Twelve) : pushGuard ⟨88,68,108,108,.south,1,1,false,false⟩ 0 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push101_0 : PushBound ⟨88,68,108,108,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push101_0]; exact allowed)
  have checked := c17768 pattern guarded
  change d476 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push101_1 (pattern : Twelve) : pushGuard ⟨88,68,108,108,.south,1,1,false,false⟩ 1 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push101_1 : PushBound ⟨88,68,108,108,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push101_1]; exact allowed)
  have checked := c17824 pattern guarded
  change d1104 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push101_2 (pattern : Twelve) : pushGuard ⟨88,68,108,108,.south,1,1,false,false⟩ 2 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push101_2 : PushBound ⟨88,68,108,108,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push101_2]; exact allowed)
  have checked := c17863 pattern guarded
  change d1492 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push101_3 (pattern : Twelve) : pushGuard ⟨88,68,108,108,.south,1,1,false,false⟩ 3 pattern = decide (d1852 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> rfl
theorem push101_3 : PushBound ⟨88,68,108,108,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1852 pattern = 1 := of_decide_eq_true (by rw [← guard_push101_3]; exact allowed)
  have checked := c17889 pattern guarded
  change d1744 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push102_0 (pattern : Twelve) : pushGuard ⟨90,110,70,70,.north,1,1,false,false⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push102_0 : PushBound ⟨90,110,70,70,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_0]; exact allowed)
  have checked := c12784 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 10)
  rw [s1727]
  exact checked
theorem guard_push102_1 (pattern : Twelve) : pushGuard ⟨90,110,70,70,.north,1,1,false,false⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push102_1 : PushBound ⟨90,110,70,70,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_1]; exact allowed)
  have checked := c12857 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 10)
  rw [s1798]
  exact checked
theorem guard_push102_2 (pattern : Twelve) : pushGuard ⟨90,110,70,70,.north,1,1,false,false⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push102_2 : PushBound ⟨90,110,70,70,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_2]; exact allowed)
  have checked := c12923 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 10)
  rw [s1861]
  exact checked
theorem guard_push102_3 (pattern : Twelve) : pushGuard ⟨90,110,70,70,.north,1,1,false,false⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push102_3 : PushBound ⟨90,110,70,70,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_3]; exact allowed)
  have checked := c12960 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 10)
  rw [s1899]
  exact checked
theorem guard_push103_0 (pattern : Twelve) : pushGuard ⟨90,70,110,110,.south,1,1,false,false⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push103_0 : PushBound ⟨90,70,110,110,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_0]; exact allowed)
  have checked := c18025 pattern guarded
  change d629 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push103_1 (pattern : Twelve) : pushGuard ⟨90,70,110,110,.south,1,1,false,false⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push103_1 : PushBound ⟨90,70,110,110,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_1]; exact allowed)
  have checked := c18108 pattern guarded
  change d1182 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push103_2 (pattern : Twelve) : pushGuard ⟨90,70,110,110,.south,1,1,false,false⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push103_2 : PushBound ⟨90,70,110,110,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_2]; exact allowed)
  have checked := c18179 pattern guarded
  change d1556 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push103_3 (pattern : Twelve) : pushGuard ⟨90,70,110,110,.south,1,1,false,false⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push103_3 : PushBound ⟨90,70,110,110,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_3]; exact allowed)
  have checked := c18217 pattern guarded
  change d1779 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push104_0 : PushBound ⟨92,112,72,72,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push104_1 (pattern : Twelve) : pushGuard ⟨92,112,72,72,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push104_1 : PushBound ⟨92,112,72,72,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push104_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push104_2 (pattern : Twelve) : pushGuard ⟨92,112,72,72,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push104_2 : PushBound ⟨92,112,72,72,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push104_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push104_3 (pattern : Twelve) : pushGuard ⟨92,112,72,72,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push104_3 : PushBound ⟨92,112,72,72,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push104_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push105_0 : PushBound ⟨92,72,112,112,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push105_1 (pattern : Twelve) : pushGuard ⟨92,72,112,112,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push105_1 : PushBound ⟨92,72,112,112,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push105_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push105_2 (pattern : Twelve) : pushGuard ⟨92,72,112,112,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push105_2 : PushBound ⟨92,72,112,112,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push105_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push105_3 (pattern : Twelve) : pushGuard ⟨92,72,112,112,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push105_3 : PushBound ⟨92,72,112,112,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push105_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push106_0 : PushBound ⟨94,114,74,74,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push106_1 (pattern : Twelve) : pushGuard ⟨94,114,74,74,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push106_1 : PushBound ⟨94,114,74,74,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push106_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push106_2 (pattern : Twelve) : pushGuard ⟨94,114,74,74,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push106_2 : PushBound ⟨94,114,74,74,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push106_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push106_3 (pattern : Twelve) : pushGuard ⟨94,114,74,74,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push106_3 : PushBound ⟨94,114,74,74,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push106_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push107_0 : PushBound ⟨94,74,114,114,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push107_1 (pattern : Twelve) : pushGuard ⟨94,74,114,114,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push107_1 : PushBound ⟨94,74,114,114,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push107_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push107_2 (pattern : Twelve) : pushGuard ⟨94,74,114,114,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push107_2 : PushBound ⟨94,74,114,114,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push107_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push107_3 (pattern : Twelve) : pushGuard ⟨94,74,114,114,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push107_3 : PushBound ⟨94,74,114,114,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push107_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
end NetHack.Sokoban21
