/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers53
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push33_0 (pattern : Twelve) : pushGuard ⟨45,25,65,65,.south,0,3,false,false⟩ 0 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push33_0 : PushBound ⟨45,25,65,65,.south,0,3,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_0]; exact allowed)
  have checked := c10927 pattern guarded
  change d116 pattern ≤ (0 : Int) + d234 (change pattern 3 2)
  rw [s802]
  exact checked
theorem guard_push33_1 (pattern : Twelve) : pushGuard ⟨45,25,65,65,.south,0,3,false,false⟩ 1 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push33_1 : PushBound ⟨45,25,65,65,.south,0,3,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_1]; exact allowed)
  have checked := c10982 pattern guarded
  change d871 pattern ≤ (0 : Int) + d939 (change pattern 3 2)
  rw [s845]
  exact checked
theorem guard_push33_2 (pattern : Twelve) : pushGuard ⟨45,25,65,65,.south,0,3,false,false⟩ 2 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push33_2 : PushBound ⟨45,25,65,65,.south,0,3,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_2]; exact allowed)
  have checked := c11024 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1379 (change pattern 3 2)
  rw [s882]
  exact checked
theorem guard_push33_3 (pattern : Twelve) : pushGuard ⟨45,25,65,65,.south,0,3,false,false⟩ 3 pattern = decide (d1890 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases c <;> cases d <;> rfl
theorem push33_3 : PushBound ⟨45,25,65,65,.south,0,3,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1890 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_3]; exact allowed)
  have checked := c11047 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1688 (change pattern 3 2)
  rw [s898]
  exact checked
theorem guard_push34_0 (pattern : Twelve) : pushGuard ⟨47,67,27,27,.north,1,1,false,true⟩ 0 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push34_0 : PushBound ⟨47,67,27,27,.north,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_0]; exact allowed)
  have checked := c11209 pattern guarded
  change d424 pattern ≤ (1 : Int) + d979 (change pattern 7 12)
  rw [s981]
  exact checked
theorem guard_push34_1 (pattern : Twelve) : pushGuard ⟨47,67,27,27,.north,1,1,false,true⟩ 1 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push34_1 : PushBound ⟨47,67,27,27,.north,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_1]; exact allowed)
  have checked := c11330 pattern guarded
  change d1069 pattern ≤ (1 : Int) + d1411 (change pattern 7 12)
  rw [s1023]
  exact checked
theorem guard_push34_2 (pattern : Twelve) : pushGuard ⟨47,67,27,27,.north,1,1,false,true⟩ 2 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push34_2 : PushBound ⟨47,67,27,27,.north,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_2]; exact allowed)
  have checked := c11402 pattern guarded
  change d1471 pattern ≤ (1 : Int) + d1704 (change pattern 7 12)
  rw [s1047]
  exact checked
theorem guard_push34_3 (pattern : Twelve) : pushGuard ⟨47,67,27,27,.north,1,1,false,true⟩ 3 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push34_3 : PushBound ⟨47,67,27,27,.north,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_3]; exact allowed)
  have checked := c11441 pattern guarded
  change d1729 pattern ≤ (1 : Int) + d6 (change pattern 7 12)
  rw [s953]
  exact checked
theorem guard_push35_0 (pattern : Twelve) : pushGuard ⟨47,27,67,67,.south,0,1,false,false⟩ 0 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push35_0 : PushBound ⟨47,27,67,67,.south,0,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_0]; exact allowed)
  have checked := c11553 pattern guarded
  change d116 pattern ≤ (0 : Int) + d303 (change pattern 7 8)
  rw [s1135]
  exact checked
theorem guard_push35_1 (pattern : Twelve) : pushGuard ⟨47,27,67,67,.south,0,1,false,false⟩ 1 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push35_1 : PushBound ⟨47,27,67,67,.south,0,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_1]; exact allowed)
  have checked := c11634 pattern guarded
  change d871 pattern ≤ (0 : Int) + d979 (change pattern 7 8)
  rw [s1187]
  exact checked
theorem guard_push35_2 (pattern : Twelve) : pushGuard ⟨47,27,67,67,.south,0,1,false,false⟩ 2 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push35_2 : PushBound ⟨47,27,67,67,.south,0,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_2]; exact allowed)
  have checked := c11698 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1411 (change pattern 7 8)
  rw [s1230]
  exact checked
theorem guard_push35_3 (pattern : Twelve) : pushGuard ⟨47,27,67,67,.south,0,1,false,false⟩ 3 pattern = decide (d1901 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push35_3 : PushBound ⟨47,27,67,67,.south,0,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1901 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_3]; exact allowed)
  have checked := c11726 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1704 (change pattern 7 8)
  rw [s1254]
  exact checked
theorem guard_push36_0 (pattern : Twelve) : pushGuard ⟨48,68,28,28,.north,1,1,false,true⟩ 0 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push36_0 : PushBound ⟨48,68,28,28,.north,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_0]; exact allowed)
  have checked := c11839 pattern guarded
  change d476 pattern ≤ (1 : Int) + d1010 (change pattern 4 12)
  rw [s1330]
  exact checked
theorem guard_push36_1 (pattern : Twelve) : pushGuard ⟨48,68,28,28,.north,1,1,false,true⟩ 1 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push36_1 : PushBound ⟨48,68,28,28,.north,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_1]; exact allowed)
  have checked := c11896 pattern guarded
  change d1104 pattern ≤ (1 : Int) + d1427 (change pattern 4 12)
  rw [s1372]
  exact checked
theorem guard_push36_2 (pattern : Twelve) : pushGuard ⟨48,68,28,28,.north,1,1,false,true⟩ 2 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push36_2 : PushBound ⟨48,68,28,28,.north,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_2]; exact allowed)
  have checked := c11941 pattern guarded
  change d1492 pattern ≤ (1 : Int) + d1713 (change pattern 4 12)
  rw [s1408]
  exact checked
theorem guard_push36_3 (pattern : Twelve) : pushGuard ⟨48,68,28,28,.north,1,1,false,true⟩ 3 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push36_3 : PushBound ⟨48,68,28,28,.north,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_3]; exact allowed)
  have checked := c11970 pattern guarded
  change d1744 pattern ≤ (1 : Int) + d6 (change pattern 4 12)
  rw [s1267]
  exact checked
theorem guard_push37_0 (pattern : Twelve) : pushGuard ⟨48,28,68,68,.south,1,1,false,false⟩ 0 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push37_0 : PushBound ⟨48,28,68,68,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_0]; exact allowed)
  have checked := c12050 pattern guarded
  change d116 pattern ≤ (1 : Int) + d344 (change pattern 4 5)
  rw [s1493]
  exact checked
theorem guard_push37_1 (pattern : Twelve) : pushGuard ⟨48,28,68,68,.south,1,1,false,false⟩ 1 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push37_1 : PushBound ⟨48,28,68,68,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_1]; exact allowed)
  have checked := c12113 pattern guarded
  change d871 pattern ≤ (1 : Int) + d1010 (change pattern 4 5)
  rw [s1548]
  exact checked
theorem guard_push37_2 (pattern : Twelve) : pushGuard ⟨48,28,68,68,.south,1,1,false,false⟩ 2 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push37_2 : PushBound ⟨48,28,68,68,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_2]; exact allowed)
  have checked := c12180 pattern guarded
  change d1323 pattern ≤ (1 : Int) + d1427 (change pattern 4 5)
  rw [s1585]
  exact checked
theorem guard_push37_3 (pattern : Twelve) : pushGuard ⟨48,28,68,68,.south,1,1,false,false⟩ 3 pattern = decide (d1999 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push37_3 : PushBound ⟨48,28,68,68,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1999 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_3]; exact allowed)
  have checked := c12207 pattern guarded
  change d1664 pattern ≤ (1 : Int) + d1713 (change pattern 4 5)
  rw [s1610]
  exact checked
theorem guard_push38_0 (pattern : Twelve) : pushGuard ⟨50,70,30,30,.north,1,1,false,true⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push38_0 : PushBound ⟨50,70,30,30,.north,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_0]; exact allowed)
  have checked := c12446 pattern guarded
  change d629 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push38_1 (pattern : Twelve) : pushGuard ⟨50,70,30,30,.north,1,1,false,true⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push38_1 : PushBound ⟨50,70,30,30,.north,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_1]; exact allowed)
  have checked := c12558 pattern guarded
  change d1182 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push38_2 (pattern : Twelve) : pushGuard ⟨50,70,30,30,.north,1,1,false,true⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push38_2 : PushBound ⟨50,70,30,30,.north,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_2]; exact allowed)
  have checked := c12630 pattern guarded
  change d1556 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push38_3 (pattern : Twelve) : pushGuard ⟨50,70,30,30,.north,1,1,false,true⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push38_3 : PushBound ⟨50,70,30,30,.north,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_3]; exact allowed)
  have checked := c12673 pattern guarded
  change d1779 pattern ≤ (1 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push39_0 (pattern : Twelve) : pushGuard ⟨50,30,70,70,.south,1,1,false,false⟩ 0 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push39_0 : PushBound ⟨50,30,70,70,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_0]; exact allowed)
  have checked := c12784 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 10)
  rw [s1727]
  exact checked
theorem guard_push39_1 (pattern : Twelve) : pushGuard ⟨50,30,70,70,.south,1,1,false,false⟩ 1 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push39_1 : PushBound ⟨50,30,70,70,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_1]; exact allowed)
  have checked := c12857 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 10)
  rw [s1798]
  exact checked
theorem guard_push39_2 (pattern : Twelve) : pushGuard ⟨50,30,70,70,.south,1,1,false,false⟩ 2 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push39_2 : PushBound ⟨50,30,70,70,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_2]; exact allowed)
  have checked := c12923 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 10)
  rw [s1861]
  exact checked
theorem guard_push39_3 (pattern : Twelve) : pushGuard ⟨50,30,70,70,.south,1,1,false,false⟩ 3 pattern = decide (d1865 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push39_3 : PushBound ⟨50,30,70,70,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1865 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_3]; exact allowed)
  have checked := c12960 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 10)
  rw [s1899]
  exact checked
theorem push40_0 : PushBound ⟨52,72,32,32,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push40_1 (pattern : Twelve) : pushGuard ⟨52,72,32,32,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push40_1 : PushBound ⟨52,72,32,32,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push40_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push40_2 (pattern : Twelve) : pushGuard ⟨52,72,32,32,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push40_2 : PushBound ⟨52,72,32,32,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push40_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push40_3 (pattern : Twelve) : pushGuard ⟨52,72,32,32,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push40_3 : PushBound ⟨52,72,32,32,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push40_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push41_0 : PushBound ⟨52,32,72,72,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push41_1 (pattern : Twelve) : pushGuard ⟨52,32,72,72,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push41_1 : PushBound ⟨52,32,72,72,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push41_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push41_2 (pattern : Twelve) : pushGuard ⟨52,32,72,72,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push41_2 : PushBound ⟨52,32,72,72,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push41_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push41_3 (pattern : Twelve) : pushGuard ⟨52,32,72,72,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push41_3 : PushBound ⟨52,32,72,72,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push41_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push42_0 : PushBound ⟨54,74,34,34,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push42_1 (pattern : Twelve) : pushGuard ⟨54,74,34,34,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push42_1 : PushBound ⟨54,74,34,34,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push42_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push42_2 (pattern : Twelve) : pushGuard ⟨54,74,34,34,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push42_2 : PushBound ⟨54,74,34,34,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push42_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push42_3 (pattern : Twelve) : pushGuard ⟨54,74,34,34,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push42_3 : PushBound ⟨54,74,34,34,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push42_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push43_0 : PushBound ⟨54,34,74,74,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push43_1 (pattern : Twelve) : pushGuard ⟨54,34,74,74,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push43_1 : PushBound ⟨54,34,74,74,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push43_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push43_2 (pattern : Twelve) : pushGuard ⟨54,34,74,74,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push43_2 : PushBound ⟨54,34,74,74,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push43_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push43_3 (pattern : Twelve) : pushGuard ⟨54,34,74,74,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push43_3 : PushBound ⟨54,34,74,74,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push43_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push44_0 : PushBound ⟨55,75,35,35,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push44_1 (pattern : Twelve) : pushGuard ⟨55,75,35,35,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push44_1 : PushBound ⟨55,75,35,35,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push44_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push44_2 (pattern : Twelve) : pushGuard ⟨55,75,35,35,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push44_2 : PushBound ⟨55,75,35,35,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push44_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push44_3 (pattern : Twelve) : pushGuard ⟨55,75,35,35,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push44_3 : PushBound ⟨55,75,35,35,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push44_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push45_0 : PushBound ⟨55,54,56,56,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push45_1 (pattern : Twelve) : pushGuard ⟨55,54,56,56,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push45_1 : PushBound ⟨55,54,56,56,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push45_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
end NetHack.Sokoban21
