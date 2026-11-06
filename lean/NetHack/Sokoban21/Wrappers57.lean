/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers56
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push70_2 (pattern : Twelve) : pushGuard ⟨67,47,87,87,.south,2,2,false,false⟩ 2 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push70_2 : PushBound ⟨67,47,87,87,.south,2,2,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_2]; exact allowed)
  have checked := c14914 pattern guarded
  change d1411 pattern ≤ (2 : Int) + d1471 (change pattern 8 12)
  rw [s3074]
  exact checked
theorem guard_push70_3 (pattern : Twelve) : pushGuard ⟨67,47,87,87,.south,2,2,false,false⟩ 3 pattern = decide (d2301 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases h <;> cases i <;> rfl
theorem push70_3 : PushBound ⟨67,47,87,87,.south,2,2,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2301 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_3]; exact allowed)
  have checked := c14944 pattern guarded
  change d1704 pattern ≤ (2 : Int) + d1729 (change pattern 8 12)
  rw [s3096]
  exact checked
theorem guard_push71_0 (pattern : Twelve) : pushGuard ⟨67,68,66,66,.west,0,2,false,false⟩ 0 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push71_0 : PushBound ⟨67,68,66,66,.west,0,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_0]; exact allowed)
  have checked := c15016 pattern guarded
  change d476 pattern ≤ (0 : Int) + d424 (change pattern 8 9)
  rw [s3170]
  exact checked
theorem guard_push71_1 (pattern : Twelve) : pushGuard ⟨67,68,66,66,.west,0,2,false,false⟩ 1 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push71_1 : PushBound ⟨67,68,66,66,.west,0,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_1]; exact allowed)
  have checked := c15076 pattern guarded
  change d1104 pattern ≤ (0 : Int) + d1069 (change pattern 8 9)
  rw [s3214]
  exact checked
theorem guard_push71_2 (pattern : Twelve) : pushGuard ⟨67,68,66,66,.west,0,2,false,false⟩ 2 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push71_2 : PushBound ⟨67,68,66,66,.west,0,2,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_2]; exact allowed)
  have checked := c15119 pattern guarded
  change d1492 pattern ≤ (0 : Int) + d1471 (change pattern 8 9)
  rw [s3249]
  exact checked
theorem guard_push71_3 (pattern : Twelve) : pushGuard ⟨67,68,66,66,.west,0,2,false,false⟩ 3 pattern = decide (d2356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push71_3 : PushBound ⟨67,68,66,66,.west,0,2,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2356 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_3]; exact allowed)
  have checked := c15149 pattern guarded
  change d1744 pattern ≤ (0 : Int) + d1729 (change pattern 8 9)
  rw [s3271]
  exact checked
theorem guard_push72_0 (pattern : Twelve) : pushGuard ⟨68,88,48,48,.north,1,1,false,false⟩ 0 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push72_0 : PushBound ⟨68,88,48,48,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_0]; exact allowed)
  have checked := c15231 pattern guarded
  change d156 pattern ≤ (1 : Int) + d476 (change pattern 5 4)
  rw [s3336]
  exact checked
theorem guard_push72_1 (pattern : Twelve) : pushGuard ⟨68,88,48,48,.north,1,1,false,false⟩ 1 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push72_1 : PushBound ⟨68,88,48,48,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_1]; exact allowed)
  have checked := c15299 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1104 (change pattern 5 4)
  rw [s3391]
  exact checked
theorem guard_push72_2 (pattern : Twelve) : pushGuard ⟨68,88,48,48,.north,1,1,false,false⟩ 2 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push72_2 : PushBound ⟨68,88,48,48,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_2]; exact allowed)
  have checked := c15369 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1492 (change pattern 5 4)
  rw [s3438]
  exact checked
theorem guard_push72_3 (pattern : Twelve) : pushGuard ⟨68,88,48,48,.north,1,1,false,false⟩ 3 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push72_3 : PushBound ⟨68,88,48,48,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_3]; exact allowed)
  have checked := c15415 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1744 (change pattern 5 4)
  rw [s3459]
  exact checked
theorem guard_push73_0 (pattern : Twelve) : pushGuard ⟨68,48,88,88,.south,1,1,false,false⟩ 0 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push73_0 : PushBound ⟨68,48,88,88,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_0]; exact allowed)
  have checked := c15501 pattern guarded
  change d344 pattern ≤ (1 : Int) + d476 (change pattern 5 12)
  rw [s3537]
  exact checked
theorem guard_push73_1 (pattern : Twelve) : pushGuard ⟨68,48,88,88,.south,1,1,false,false⟩ 1 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push73_1 : PushBound ⟨68,48,88,88,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_1]; exact allowed)
  have checked := c15576 pattern guarded
  change d1010 pattern ≤ (1 : Int) + d1104 (change pattern 5 12)
  rw [s3593]
  exact checked
theorem guard_push73_2 (pattern : Twelve) : pushGuard ⟨68,48,88,88,.south,1,1,false,false⟩ 2 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push73_2 : PushBound ⟨68,48,88,88,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_2]; exact allowed)
  have checked := c15623 pattern guarded
  change d1427 pattern ≤ (1 : Int) + d1492 (change pattern 5 12)
  rw [s3637]
  exact checked
theorem guard_push73_3 (pattern : Twelve) : pushGuard ⟨68,48,88,88,.south,1,1,false,false⟩ 3 pattern = decide (d2496 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases e <;> cases f <;> rfl
theorem push73_3 : PushBound ⟨68,48,88,88,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2496 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_3]; exact allowed)
  have checked := c15654 pattern guarded
  change d1713 pattern ≤ (1 : Int) + d1744 (change pattern 5 12)
  rw [s3658]
  exact checked
theorem guard_push74_0 (pattern : Twelve) : pushGuard ⟨70,90,50,50,.north,1,1,false,false⟩ 0 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push74_0 : PushBound ⟨70,90,50,50,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push74_0]; exact allowed)
  have checked := c15761 pattern guarded
  change d156 pattern ≤ (1 : Int) + d629 (change pattern 10 12)
  rw [s3829]
  exact checked
theorem guard_push74_1 (pattern : Twelve) : pushGuard ⟨70,90,50,50,.north,1,1,false,false⟩ 1 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push74_1 : PushBound ⟨70,90,50,50,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push74_1]; exact allowed)
  have checked := c15832 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1182 (change pattern 10 12)
  rw [s3911]
  exact checked
theorem guard_push74_2 (pattern : Twelve) : pushGuard ⟨70,90,50,50,.north,1,1,false,false⟩ 2 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push74_2 : PushBound ⟨70,90,50,50,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push74_2]; exact allowed)
  have checked := c15894 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1556 (change pattern 10 12)
  rw [s3977]
  exact checked
theorem guard_push74_3 (pattern : Twelve) : pushGuard ⟨70,90,50,50,.north,1,1,false,false⟩ 3 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push74_3 : PushBound ⟨70,90,50,50,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push74_3]; exact allowed)
  have checked := c15932 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1779 (change pattern 10 12)
  rw [s4015]
  exact checked
theorem guard_push75_0 (pattern : Twelve) : pushGuard ⟨70,50,90,90,.south,1,1,false,false⟩ 0 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push75_0 : PushBound ⟨70,50,90,90,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push75_0]; exact allowed)
  have checked := c15761 pattern guarded
  change d156 pattern ≤ (1 : Int) + d629 (change pattern 10 12)
  rw [s3829]
  exact checked
theorem guard_push75_1 (pattern : Twelve) : pushGuard ⟨70,50,90,90,.south,1,1,false,false⟩ 1 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push75_1 : PushBound ⟨70,50,90,90,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push75_1]; exact allowed)
  have checked := c15832 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1182 (change pattern 10 12)
  rw [s3911]
  exact checked
theorem guard_push75_2 (pattern : Twelve) : pushGuard ⟨70,50,90,90,.south,1,1,false,false⟩ 2 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push75_2 : PushBound ⟨70,50,90,90,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push75_2]; exact allowed)
  have checked := c15894 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1556 (change pattern 10 12)
  rw [s3977]
  exact checked
theorem guard_push75_3 (pattern : Twelve) : pushGuard ⟨70,50,90,90,.south,1,1,false,false⟩ 3 pattern = decide (d477 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> rfl
theorem push75_3 : PushBound ⟨70,50,90,90,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d477 pattern = 1 := of_decide_eq_true (by rw [← guard_push75_3]; exact allowed)
  have checked := c15932 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1779 (change pattern 10 12)
  rw [s4015]
  exact checked
theorem guard_push76_0 (pattern : Twelve) : pushGuard ⟨71,70,72,72,.east,1,1,false,true⟩ 0 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push76_0 : PushBound ⟨71,70,72,72,.east,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push76_0]; exact allowed)
  have checked := c16136 pattern guarded
  change d629 pattern ≤ (1 : Int) + d1246 (change pattern 11 12)
  rw [s4138]
  exact checked
theorem guard_push76_1 (pattern : Twelve) : pushGuard ⟨71,70,72,72,.east,1,1,false,true⟩ 1 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push76_1 : PushBound ⟨71,70,72,72,.east,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push76_1]; exact allowed)
  have checked := c16240 pattern guarded
  change d1182 pattern ≤ (1 : Int) + d1615 (change pattern 11 12)
  rw [s4198]
  exact checked
theorem guard_push76_2 (pattern : Twelve) : pushGuard ⟨71,70,72,72,.east,1,1,false,true⟩ 2 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push76_2 : PushBound ⟨71,70,72,72,.east,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push76_2]; exact allowed)
  have checked := c16315 pattern guarded
  change d1556 pattern ≤ (1 : Int) + d1813 (change pattern 11 12)
  rw [s4236]
  exact checked
theorem guard_push76_3 (pattern : Twelve) : pushGuard ⟨71,70,72,72,.east,1,1,false,true⟩ 3 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push76_3 : PushBound ⟨71,70,72,72,.east,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push76_3]; exact allowed)
  have checked := c16360 pattern guarded
  change d1779 pattern ≤ (1 : Int) + d6 (change pattern 11 12)
  rw [s4038]
  exact checked
theorem guard_push77_0 (pattern : Twelve) : pushGuard ⟨71,72,70,70,.west,1,1,false,false⟩ 0 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push77_0 : PushBound ⟨71,72,70,70,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push77_0]; exact allowed)
  have checked := c16472 pattern guarded
  change d156 pattern ≤ (1 : Int) + d777 (change pattern 11 10)
  rw [s4401]
  exact checked
theorem guard_push77_1 (pattern : Twelve) : pushGuard ⟨71,72,70,70,.west,1,1,false,false⟩ 1 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push77_1 : PushBound ⟨71,72,70,70,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push77_1]; exact allowed)
  have checked := c16543 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1246 (change pattern 11 10)
  rw [s4466]
  exact checked
theorem guard_push77_2 (pattern : Twelve) : pushGuard ⟨71,72,70,70,.west,1,1,false,false⟩ 2 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push77_2 : PushBound ⟨71,72,70,70,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push77_2]; exact allowed)
  have checked := c16607 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1615 (change pattern 11 10)
  rw [s4525]
  exact checked
theorem guard_push77_3 (pattern : Twelve) : pushGuard ⟨71,72,70,70,.west,1,1,false,false⟩ 3 pattern = decide (d2746 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    cases k <;> cases l <;> rfl
theorem push77_3 : PushBound ⟨71,72,70,70,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d2746 pattern = 1 := of_decide_eq_true (by rw [← guard_push77_3]; exact allowed)
  have checked := c16644 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1813 (change pattern 11 10)
  rw [s4563]
  exact checked
theorem push78_0 : PushBound ⟨72,92,52,52,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push78_1 (pattern : Twelve) : pushGuard ⟨72,92,52,52,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push78_1 : PushBound ⟨72,92,52,52,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push78_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push78_2 (pattern : Twelve) : pushGuard ⟨72,92,52,52,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push78_2 : PushBound ⟨72,92,52,52,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push78_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push78_3 (pattern : Twelve) : pushGuard ⟨72,92,52,52,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push78_3 : PushBound ⟨72,92,52,52,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push78_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push79_0 : PushBound ⟨72,52,92,92,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push79_1 (pattern : Twelve) : pushGuard ⟨72,52,92,92,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push79_1 : PushBound ⟨72,52,92,92,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push79_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push79_2 (pattern : Twelve) : pushGuard ⟨72,52,92,92,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push79_2 : PushBound ⟨72,52,92,92,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push79_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push79_3 (pattern : Twelve) : pushGuard ⟨72,52,92,92,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push79_3 : PushBound ⟨72,52,92,92,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push79_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push80_0 : PushBound ⟨74,94,54,54,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push80_1 (pattern : Twelve) : pushGuard ⟨74,94,54,54,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push80_1 : PushBound ⟨74,94,54,54,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push80_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push80_2 (pattern : Twelve) : pushGuard ⟨74,94,54,54,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push80_2 : PushBound ⟨74,94,54,54,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push80_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push80_3 (pattern : Twelve) : pushGuard ⟨74,94,54,54,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push80_3 : PushBound ⟨74,94,54,54,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push80_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push81_0 : PushBound ⟨74,54,94,94,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push81_1 (pattern : Twelve) : pushGuard ⟨74,54,94,94,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push81_1 : PushBound ⟨74,54,94,94,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push81_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push81_2 (pattern : Twelve) : pushGuard ⟨74,54,94,94,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push81_2 : PushBound ⟨74,54,94,94,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push81_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push81_3 (pattern : Twelve) : pushGuard ⟨74,54,94,94,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push81_3 : PushBound ⟨74,54,94,94,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push81_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push82_0 : PushBound ⟨75,95,55,55,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push82_1 (pattern : Twelve) : pushGuard ⟨75,95,55,55,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push82_1 : PushBound ⟨75,95,55,55,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push82_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push82_2 (pattern : Twelve) : pushGuard ⟨75,95,55,55,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push82_2 : PushBound ⟨75,95,55,55,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push82_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push82_3 (pattern : Twelve) : pushGuard ⟨75,95,55,55,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push82_3 : PushBound ⟨75,95,55,55,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push82_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
end NetHack.Sokoban21
