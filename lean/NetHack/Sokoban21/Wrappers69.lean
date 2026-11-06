/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers68
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push220_2 (pattern : Twelve) : pushGuard ⟨183,203,163,163,.north,2,16,false,false⟩ 2 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push220_2 : PushBound ⟨183,203,163,163,.north,2,16,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push220_2]; exact allowed)
  have checked := c20973 pattern guarded
  change d1323 pattern ≤ (2 : Int) + d1643 (change pattern 0 12)
  rw [s7191]
  exact checked
theorem guard_push220_3 (pattern : Twelve) : pushGuard ⟨183,203,163,163,.north,2,16,false,false⟩ 3 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push220_3 : PushBound ⟨183,203,163,163,.north,2,16,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push220_3]; exact allowed)
  have checked := c20974 pattern guarded
  change d1664 pattern ≤ (2 : Int) + d1834 (change pattern 0 12)
  rw [s7215]
  exact checked
theorem guard_push221_0 (pattern : Twelve) : pushGuard ⟨183,182,184,184,.east,0,16,false,false⟩ 0 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push221_0 : PushBound ⟨183,182,184,184,.east,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push221_0]; exact allowed)
  have checked := c20975 pattern guarded
  change d116 pattern ≤ (0 : Int) + d813 (change pattern 0 12)
  rw [s7078]
  exact checked
theorem guard_push221_1 (pattern : Twelve) : pushGuard ⟨183,182,184,184,.east,0,16,false,false⟩ 1 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push221_1 : PushBound ⟨183,182,184,184,.east,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push221_1]; exact allowed)
  have checked := c20976 pattern guarded
  change d871 pattern ≤ (0 : Int) + d1274 (change pattern 0 12)
  rw [s7137]
  exact checked
theorem guard_push221_2 (pattern : Twelve) : pushGuard ⟨183,182,184,184,.east,0,16,false,false⟩ 2 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push221_2 : PushBound ⟨183,182,184,184,.east,0,16,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push221_2]; exact allowed)
  have checked := c20977 pattern guarded
  change d1323 pattern ≤ (0 : Int) + d1643 (change pattern 0 12)
  rw [s7191]
  exact checked
theorem guard_push221_3 (pattern : Twelve) : pushGuard ⟨183,182,184,184,.east,0,16,false,false⟩ 3 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push221_3 : PushBound ⟨183,182,184,184,.east,0,16,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push221_3]; exact allowed)
  have checked := c20978 pattern guarded
  change d1664 pattern ≤ (0 : Int) + d1834 (change pattern 0 12)
  rw [s7215]
  exact checked
theorem guard_push222_0 (pattern : Twelve) : pushGuard ⟨183,163,203,203,.south,16,16,false,true⟩ 0 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push222_0 : PushBound ⟨183,163,203,203,.south,16,16,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push222_0]; exact allowed)
  have checked := c20979 pattern guarded
  change d116 pattern ≤ (16 : Int) + d1274 (change pattern 0 12)
  rw [s7137]
  exact checked
theorem guard_push222_1 (pattern : Twelve) : pushGuard ⟨183,163,203,203,.south,16,16,false,true⟩ 1 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push222_1 : PushBound ⟨183,163,203,203,.south,16,16,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push222_1]; exact allowed)
  have checked := c20980 pattern guarded
  change d871 pattern ≤ (16 : Int) + d1643 (change pattern 0 12)
  rw [s7191]
  exact checked
theorem guard_push222_2 (pattern : Twelve) : pushGuard ⟨183,163,203,203,.south,16,16,false,true⟩ 2 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push222_2 : PushBound ⟨183,163,203,203,.south,16,16,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push222_2]; exact allowed)
  have checked := c20981 pattern guarded
  change d1323 pattern ≤ (16 : Int) + d1834 (change pattern 0 12)
  rw [s7215]
  exact checked
theorem guard_push222_3 (pattern : Twelve) : pushGuard ⟨183,163,203,203,.south,16,16,false,true⟩ 3 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push222_3 : PushBound ⟨183,163,203,203,.south,16,16,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push222_3]; exact allowed)
  have checked := c20982 pattern guarded
  change d1664 pattern ≤ (16 : Int) + d6 (change pattern 0 12)
  rw [s6978]
  exact checked
theorem guard_push223_0 (pattern : Twelve) : pushGuard ⟨183,184,182,182,.west,2,16,false,false⟩ 0 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push223_0 : PushBound ⟨183,184,182,182,.west,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push223_0]; exact allowed)
  have checked := c21083 pattern guarded
  change d806 pattern ≤ (2 : Int) + d813 (change pattern 0 12)
  rw [s7078]
  exact checked
theorem guard_push223_1 (pattern : Twelve) : pushGuard ⟨183,184,182,182,.west,2,16,false,false⟩ 1 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push223_1 : PushBound ⟨183,184,182,182,.west,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push223_1]; exact allowed)
  have checked := c21153 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1274 (change pattern 0 12)
  rw [s7137]
  exact checked
theorem guard_push223_2 (pattern : Twelve) : pushGuard ⟨183,184,182,182,.west,2,16,false,false⟩ 2 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push223_2 : PushBound ⟨183,184,182,182,.west,2,16,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push223_2]; exact allowed)
  have checked := c21219 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1643 (change pattern 0 12)
  rw [s7191]
  exact checked
theorem guard_push223_3 (pattern : Twelve) : pushGuard ⟨183,184,182,182,.west,2,16,false,false⟩ 3 pattern = decide (d1879 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push223_3 : PushBound ⟨183,184,182,182,.west,2,16,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1879 pattern = 1 := of_decide_eq_true (by rw [← guard_push223_3]; exact allowed)
  have checked := c21261 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1834 (change pattern 0 12)
  rw [s7215]
  exact checked
theorem guard_push224_0 (pattern : Twelve) : pushGuard ⟨184,183,185,185,.east,0,17,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push224_0 : PushBound ⟨184,183,185,185,.east,0,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push224_0]; exact allowed)
  have checked := c9792 pattern guarded
  change d813 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push224_1 (pattern : Twelve) : pushGuard ⟨184,183,185,185,.east,0,17,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push224_1 : PushBound ⟨184,183,185,185,.east,0,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push224_1]; exact allowed)
  have checked := c9793 pattern guarded
  change d1274 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push224_2 (pattern : Twelve) : pushGuard ⟨184,183,185,185,.east,0,17,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push224_2 : PushBound ⟨184,183,185,185,.east,0,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push224_2]; exact allowed)
  have checked := c9794 pattern guarded
  change d1643 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push224_3 (pattern : Twelve) : pushGuard ⟨184,183,185,185,.east,0,17,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push224_3 : PushBound ⟨184,183,185,185,.east,0,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push224_3]; exact allowed)
  have checked := c9795 pattern guarded
  change d1834 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push225_0 (pattern : Twelve) : pushGuard ⟨184,185,183,183,.west,2,17,false,false⟩ 0 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push225_0 : PushBound ⟨184,185,183,183,.west,2,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push225_0]; exact allowed)
  have checked := c21362 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 0)
  rw [s7279]
  exact checked
theorem guard_push225_1 (pattern : Twelve) : pushGuard ⟨184,185,183,183,.west,2,17,false,false⟩ 1 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push225_1 : PushBound ⟨184,185,183,183,.west,2,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push225_1]; exact allowed)
  have checked := c21433 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 0)
  rw [s7334]
  exact checked
theorem guard_push225_2 (pattern : Twelve) : pushGuard ⟨184,185,183,183,.west,2,17,false,false⟩ 2 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push225_2 : PushBound ⟨184,185,183,183,.west,2,17,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push225_2]; exact allowed)
  have checked := c21502 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 0)
  rw [s7385]
  exact checked
theorem guard_push225_3 (pattern : Twelve) : pushGuard ⟨184,185,183,183,.west,2,17,false,false⟩ 3 pattern = decide (d1878 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases a <;> rfl
theorem push225_3 : PushBound ⟨184,185,183,183,.west,2,17,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1878 pattern = 1 := of_decide_eq_true (by rw [← guard_push225_3]; exact allowed)
  have checked := c21536 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 0)
  rw [s7413]
  exact checked
theorem guard_push226_0 (pattern : Twelve) : pushGuard ⟨185,205,165,165,.north,2,18,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push226_0 : PushBound ⟨185,205,165,165,.north,2,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push226_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push226_1 (pattern : Twelve) : pushGuard ⟨185,205,165,165,.north,2,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push226_1 : PushBound ⟨185,205,165,165,.north,2,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push226_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push226_2 (pattern : Twelve) : pushGuard ⟨185,205,165,165,.north,2,18,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push226_2 : PushBound ⟨185,205,165,165,.north,2,18,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push226_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push226_3 (pattern : Twelve) : pushGuard ⟨185,205,165,165,.north,2,18,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push226_3 : PushBound ⟨185,205,165,165,.north,2,18,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push226_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push227_0 (pattern : Twelve) : pushGuard ⟨185,184,186,186,.east,0,18,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push227_0 : PushBound ⟨185,184,186,186,.east,0,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push227_0]; exact allowed)
  have checked := c9772 pattern guarded
  change d806 pattern ≤ (0 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push227_1 (pattern : Twelve) : pushGuard ⟨185,184,186,186,.east,0,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push227_1 : PushBound ⟨185,184,186,186,.east,0,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push227_1]; exact allowed)
  have checked := c9773 pattern guarded
  change d1267 pattern ≤ (0 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push227_2 (pattern : Twelve) : pushGuard ⟨185,184,186,186,.east,0,18,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push227_2 : PushBound ⟨185,184,186,186,.east,0,18,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push227_2]; exact allowed)
  have checked := c9774 pattern guarded
  change d1636 pattern ≤ (0 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push227_3 (pattern : Twelve) : pushGuard ⟨185,184,186,186,.east,0,18,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push227_3 : PushBound ⟨185,184,186,186,.east,0,18,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push227_3]; exact allowed)
  have checked := c9775 pattern guarded
  change d1827 pattern ≤ (0 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push228_0 (pattern : Twelve) : pushGuard ⟨185,165,205,205,.south,18,18,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push228_0 : PushBound ⟨185,165,205,205,.south,18,18,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push228_0]; exact allowed)
  have checked := c21768 pattern guarded
  change d806 pattern ≤ (18 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push228_1 (pattern : Twelve) : pushGuard ⟨185,165,205,205,.south,18,18,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push228_1 : PushBound ⟨185,165,205,205,.south,18,18,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push228_1]; exact allowed)
  have checked := c21912 pattern guarded
  change d1267 pattern ≤ (18 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push228_2 (pattern : Twelve) : pushGuard ⟨185,165,205,205,.south,18,18,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push228_2 : PushBound ⟨185,165,205,205,.south,18,18,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push228_2]; exact allowed)
  have checked := c22015 pattern guarded
  change d1636 pattern ≤ (18 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push228_3 (pattern : Twelve) : pushGuard ⟨185,165,205,205,.south,18,18,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push228_3 : PushBound ⟨185,165,205,205,.south,18,18,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push228_3]; exact allowed)
  have checked := c22069 pattern guarded
  change d1827 pattern ≤ (18 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push229_0 (pattern : Twelve) : pushGuard ⟨185,186,184,184,.west,2,18,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push229_0 : PushBound ⟨185,186,184,184,.west,2,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push229_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push229_1 (pattern : Twelve) : pushGuard ⟨185,186,184,184,.west,2,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push229_1 : PushBound ⟨185,186,184,184,.west,2,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push229_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push229_2 (pattern : Twelve) : pushGuard ⟨185,186,184,184,.west,2,18,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push229_2 : PushBound ⟨185,186,184,184,.west,2,18,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push229_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push229_3 (pattern : Twelve) : pushGuard ⟨185,186,184,184,.west,2,18,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push229_3 : PushBound ⟨185,186,184,184,.west,2,18,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push229_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push230_0 (pattern : Twelve) : pushGuard ⟨186,206,166,166,.north,2,19,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push230_0 : PushBound ⟨186,206,166,166,.north,2,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push230_0]; exact allowed)
  have checked := c20641 pattern guarded
  change d806 pattern ≤ (2 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push230_1 (pattern : Twelve) : pushGuard ⟨186,206,166,166,.north,2,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push230_1 : PushBound ⟨186,206,166,166,.north,2,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push230_1]; exact allowed)
  have checked := c20642 pattern guarded
  change d1267 pattern ≤ (2 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push230_2 (pattern : Twelve) : pushGuard ⟨186,206,166,166,.north,2,19,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push230_2 : PushBound ⟨186,206,166,166,.north,2,19,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push230_2]; exact allowed)
  have checked := c20643 pattern guarded
  change d1636 pattern ≤ (2 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push230_3 (pattern : Twelve) : pushGuard ⟨186,206,166,166,.north,2,19,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push230_3 : PushBound ⟨186,206,166,166,.north,2,19,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push230_3]; exact allowed)
  have checked := c20644 pattern guarded
  change d1827 pattern ≤ (2 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push231_0 (pattern : Twelve) : pushGuard ⟨186,185,187,186,.east,1,19,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push231_0 : PushBound ⟨186,185,187,186,.east,1,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push231_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push231_1 (pattern : Twelve) : pushGuard ⟨186,185,187,186,.east,1,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push231_1 : PushBound ⟨186,185,187,186,.east,1,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push231_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push231_2 (pattern : Twelve) : pushGuard ⟨186,185,187,186,.east,1,19,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push231_2 : PushBound ⟨186,185,187,186,.east,1,19,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push231_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push231_3 (pattern : Twelve) : pushGuard ⟨186,185,187,186,.east,1,19,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push231_3 : PushBound ⟨186,185,187,186,.east,1,19,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push231_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
theorem guard_push232_0 (pattern : Twelve) : pushGuard ⟨186,185,187,187,.east,1,19,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push232_0 : PushBound ⟨186,185,187,187,.east,1,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push232_0]; exact allowed)
  have checked := c22070 pattern guarded
  change d806 pattern ≤ (1 : Int) + d806 (change pattern 12 12)
  rw [s6205]
  exact checked
theorem guard_push232_1 (pattern : Twelve) : pushGuard ⟨186,185,187,187,.east,1,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push232_1 : PushBound ⟨186,185,187,187,.east,1,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push232_1]; exact allowed)
  have checked := c22071 pattern guarded
  change d1267 pattern ≤ (1 : Int) + d1267 (change pattern 12 12)
  rw [s6225]
  exact checked
theorem guard_push232_2 (pattern : Twelve) : pushGuard ⟨186,185,187,187,.east,1,19,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push232_2 : PushBound ⟨186,185,187,187,.east,1,19,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push232_2]; exact allowed)
  have checked := c22072 pattern guarded
  change d1636 pattern ≤ (1 : Int) + d1636 (change pattern 12 12)
  rw [s6246]
  exact checked
theorem guard_push232_3 (pattern : Twelve) : pushGuard ⟨186,185,187,187,.east,1,19,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push232_3 : PushBound ⟨186,185,187,187,.east,1,19,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push232_3]; exact allowed)
  have checked := c22073 pattern guarded
  change d1827 pattern ≤ (1 : Int) + d1827 (change pattern 12 12)
  rw [s6260]
  exact checked
end NetHack.Sokoban21
