/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers66
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push195_2 (pattern : Twelve) : pushGuard ⟨143,123,163,163,.south,0,14,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push195_2 : PushBound ⟨143,123,163,163,.south,0,14,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push195_2]; exact allowed)
  have checked := c2 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1323 (change pattern 12 12)
  rw [s151]
  exact checked
theorem guard_push195_3 (pattern : Twelve) : pushGuard ⟨143,123,163,163,.south,0,14,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push195_3 : PushBound ⟨143,123,163,163,.south,0,14,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push195_3]; exact allowed)
  have checked := c3 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1664 (change pattern 12 12)
  rw [s176]
  exact checked
theorem guard_push196_0 (pattern : Twelve) : pushGuard ⟨145,165,125,125,.north,16,16,false,true⟩ 0 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push196_0 : PushBound ⟨145,165,125,125,.north,16,16,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push196_0]; exact allowed)
  have checked := c20204 pattern guarded
  change d806 pattern ≤ (16 : Int) + d1273 (change pattern 1 12)
  rw [s5612]
  exact checked
theorem guard_push196_1 (pattern : Twelve) : pushGuard ⟨145,165,125,125,.north,16,16,false,true⟩ 1 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push196_1 : PushBound ⟨145,165,125,125,.north,16,16,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push196_1]; exact allowed)
  have checked := c20250 pattern guarded
  change d1267 pattern ≤ (16 : Int) + d1642 (change pattern 1 12)
  rw [s5718]
  exact checked
theorem guard_push196_2 (pattern : Twelve) : pushGuard ⟨145,165,125,125,.north,16,16,false,true⟩ 2 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push196_2 : PushBound ⟨145,165,125,125,.north,16,16,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push196_2]; exact allowed)
  have checked := c20275 pattern guarded
  change d1636 pattern ≤ (16 : Int) + d1833 (change pattern 1 12)
  rw [s5769]
  exact checked
theorem guard_push196_3 (pattern : Twelve) : pushGuard ⟨145,165,125,125,.north,16,16,false,true⟩ 3 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push196_3 : PushBound ⟨145,165,125,125,.north,16,16,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push196_3]; exact allowed)
  have checked := c20280 pattern guarded
  change d1827 pattern ≤ (16 : Int) + d6 (change pattern 1 12)
  rw [s5467]
  exact checked
theorem guard_push197_0 (pattern : Twelve) : pushGuard ⟨145,125,165,165,.south,0,16,false,false⟩ 0 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push197_0 : PushBound ⟨145,125,165,165,.south,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push197_0]; exact allowed)
  have checked := c20281 pattern guarded
  change d806 pattern ≤ (0 : Int) + d812 (change pattern 1 12)
  rw [s5903]
  exact checked
theorem guard_push197_1 (pattern : Twelve) : pushGuard ⟨145,125,165,165,.south,0,16,false,false⟩ 1 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push197_1 : PushBound ⟨145,125,165,165,.south,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push197_1]; exact allowed)
  have checked := c20282 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1273 (change pattern 1 12)
  rw [s5612]
  exact checked
theorem guard_push197_2 (pattern : Twelve) : pushGuard ⟨145,125,165,165,.south,0,16,false,false⟩ 2 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push197_2 : PushBound ⟨145,125,165,165,.south,0,16,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push197_2]; exact allowed)
  have checked := c20283 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1642 (change pattern 1 12)
  rw [s5718]
  exact checked
theorem guard_push197_3 (pattern : Twelve) : pushGuard ⟨145,125,165,165,.south,0,16,false,false⟩ 3 pattern = decide (d1874 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases b <;> rfl
theorem push197_3 : PushBound ⟨145,125,165,165,.south,0,16,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1874 pattern = 1 := of_decide_eq_true (by rw [← guard_push197_3]; exact allowed)
  have checked := c20284 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1833 (change pattern 1 12)
  rw [s5769]
  exact checked
theorem guard_push198_0 (pattern : Twelve) : pushGuard ⟨146,166,126,126,.north,2,17,false,false⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push198_0 : PushBound ⟨146,166,126,126,.north,2,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push198_0]; exact allowed)
  have checked := c20420 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 6)
  rw [s6014]
  exact checked
theorem guard_push198_1 (pattern : Twelve) : pushGuard ⟨146,166,126,126,.north,2,17,false,false⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push198_1 : PushBound ⟨146,166,126,126,.north,2,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push198_1]; exact allowed)
  have checked := c20510 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 6)
  rw [s6069]
  exact checked
theorem guard_push198_2 (pattern : Twelve) : pushGuard ⟨146,166,126,126,.north,2,17,false,false⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push198_2 : PushBound ⟨146,166,126,126,.north,2,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push198_2]; exact allowed)
  have checked := c20588 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 6)
  rw [s6135]
  exact checked
theorem guard_push198_3 (pattern : Twelve) : pushGuard ⟨146,166,126,126,.north,2,17,false,false⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push198_3 : PushBound ⟨146,166,126,126,.north,2,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push198_3]; exact allowed)
  have checked := c20624 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 6)
  rw [s6176]
  exact checked
theorem guard_push199_0 (pattern : Twelve) : pushGuard ⟨146,126,166,166,.south,0,17,false,false⟩ 0 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push199_0 : PushBound ⟨146,126,166,166,.south,0,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push199_0]; exact allowed)
  have checked := c9695 pattern guarded
  change d809 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push199_1 (pattern : Twelve) : pushGuard ⟨146,126,166,166,.south,0,17,false,false⟩ 1 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push199_1 : PushBound ⟨146,126,166,166,.south,0,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push199_1]; exact allowed)
  have checked := c9700 pattern guarded
  change d1270 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push199_2 (pattern : Twelve) : pushGuard ⟨146,126,166,166,.south,0,17,false,false⟩ 2 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push199_2 : PushBound ⟨146,126,166,166,.south,0,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push199_2]; exact allowed)
  have checked := c9705 pattern guarded
  change d1639 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push199_3 (pattern : Twelve) : pushGuard ⟨146,126,166,166,.south,0,17,false,false⟩ 3 pattern = decide (d1871 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases g <;> rfl
theorem push199_3 : PushBound ⟨146,126,166,166,.south,0,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1871 pattern = 1 := of_decide_eq_true (by rw [← guard_push199_3]; exact allowed)
  have checked := c9708 pattern guarded
  change d1830 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem push200_0 : PushBound ⟨149,148,150,150,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push200_1 (pattern : Twelve) : pushGuard ⟨149,148,150,150,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push200_1 : PushBound ⟨149,148,150,150,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push200_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push200_2 (pattern : Twelve) : pushGuard ⟨149,148,150,150,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push200_2 : PushBound ⟨149,148,150,150,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push200_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push200_3 (pattern : Twelve) : pushGuard ⟨149,148,150,150,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push200_3 : PushBound ⟨149,148,150,150,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push200_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push201_0 : PushBound ⟨149,150,148,148,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push201_1 (pattern : Twelve) : pushGuard ⟨149,150,148,148,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push201_1 : PushBound ⟨149,150,148,148,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push201_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push201_2 (pattern : Twelve) : pushGuard ⟨149,150,148,148,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push201_2 : PushBound ⟨149,150,148,148,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push201_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push201_3 (pattern : Twelve) : pushGuard ⟨149,150,148,148,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push201_3 : PushBound ⟨149,150,148,148,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push201_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push202_0 : PushBound ⟨155,154,156,156,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push202_1 (pattern : Twelve) : pushGuard ⟨155,154,156,156,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push202_1 : PushBound ⟨155,154,156,156,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push202_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push202_2 (pattern : Twelve) : pushGuard ⟨155,154,156,156,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push202_2 : PushBound ⟨155,154,156,156,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push202_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push202_3 (pattern : Twelve) : pushGuard ⟨155,154,156,156,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push202_3 : PushBound ⟨155,154,156,156,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push202_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push203_0 : PushBound ⟨155,156,154,154,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push203_1 (pattern : Twelve) : pushGuard ⟨155,156,154,154,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push203_1 : PushBound ⟨155,156,154,154,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push203_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push203_2 (pattern : Twelve) : pushGuard ⟨155,156,154,154,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push203_2 : PushBound ⟨155,156,154,154,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push203_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push203_3 (pattern : Twelve) : pushGuard ⟨155,156,154,154,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push203_3 : PushBound ⟨155,156,154,154,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push203_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push204_0 : PushBound ⟨156,155,157,157,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push204_1 (pattern : Twelve) : pushGuard ⟨156,155,157,157,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push204_1 : PushBound ⟨156,155,157,157,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push204_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push204_2 (pattern : Twelve) : pushGuard ⟨156,155,157,157,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push204_2 : PushBound ⟨156,155,157,157,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push204_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push204_3 (pattern : Twelve) : pushGuard ⟨156,155,157,157,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push204_3 : PushBound ⟨156,155,157,157,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push204_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push205_0 : PushBound ⟨156,157,155,155,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push205_1 (pattern : Twelve) : pushGuard ⟨156,157,155,155,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push205_1 : PushBound ⟨156,157,155,155,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push205_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push205_2 (pattern : Twelve) : pushGuard ⟨156,157,155,155,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push205_2 : PushBound ⟨156,157,155,155,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push205_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push205_3 (pattern : Twelve) : pushGuard ⟨156,157,155,155,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push205_3 : PushBound ⟨156,157,155,155,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push205_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push206_0 : PushBound ⟨157,156,158,158,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push206_1 (pattern : Twelve) : pushGuard ⟨157,156,158,158,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push206_1 : PushBound ⟨157,156,158,158,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push206_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push206_2 (pattern : Twelve) : pushGuard ⟨157,156,158,158,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push206_2 : PushBound ⟨157,156,158,158,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push206_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push206_3 (pattern : Twelve) : pushGuard ⟨157,156,158,158,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push206_3 : PushBound ⟨157,156,158,158,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push206_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push207_0 : PushBound ⟨157,158,156,156,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push207_1 (pattern : Twelve) : pushGuard ⟨157,158,156,156,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push207_1 : PushBound ⟨157,158,156,156,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push207_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push207_2 (pattern : Twelve) : pushGuard ⟨157,158,156,156,.west,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push207_2 : PushBound ⟨157,158,156,156,.west,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push207_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push207_3 (pattern : Twelve) : pushGuard ⟨157,158,156,156,.west,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push207_3 : PushBound ⟨157,158,156,156,.west,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push207_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
end NetHack.Sokoban21
