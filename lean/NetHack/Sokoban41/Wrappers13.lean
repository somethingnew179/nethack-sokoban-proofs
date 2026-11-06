/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers12
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem push101_0 : PushBound ⟨53,39,67,67,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push101_1 (pattern : Ten) : pushGuard ⟨53,39,67,67,.south,1,1,true,true⟩ 1 pattern = decide (d379 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push101_1 : PushBound ⟨53,39,67,67,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d379 pattern = 1 := of_decide_eq_true (by rw [← guard_push101_1]; exact allowed)
  have checked := c3424 pattern guarded
  change d220 pattern ≤ (1 : Int) + d300 (change pattern 5 10)
  rw [s1204]
  exact checked
theorem guard_push102_0 (pattern : Ten) : pushGuard ⟨66,80,52,52,.north,2,10,false,false⟩ 0 pattern = decide (d568 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem push102_0 : PushBound ⟨66,80,52,52,.north,2,10,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d568 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_0]; exact allowed)
  have checked := c3451 pattern guarded
  change d170 pattern ≤ (2 : Int) + d156 (change pattern 6 4)
  rw [s1238]
  exact checked
theorem guard_push102_1 (pattern : Ten) : pushGuard ⟨66,80,52,52,.north,2,10,false,false⟩ 1 pattern = decide (d570 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem push102_1 : PushBound ⟨66,80,52,52,.north,2,10,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d570 pattern = 1 := of_decide_eq_true (by rw [← guard_push102_1]; exact allowed)
  have checked := c3487 pattern guarded
  change d349 pattern ≤ (2 : Int) + d331 (change pattern 6 4)
  rw [s1273]
  exact checked
theorem guard_push103_0 (pattern : Ten) : pushGuard ⟨66,52,80,80,.south,0,10,false,false⟩ 0 pattern = decide (d568 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem push103_0 : PushBound ⟨66,52,80,80,.south,0,10,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d568 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_0]; exact allowed)
  have checked := c3492 pattern guarded
  change d135 pattern ≤ (0 : Int) + d156 (change pattern 6 10)
  rw [s1309]
  exact checked
theorem guard_push103_1 (pattern : Ten) : pushGuard ⟨66,52,80,80,.south,0,10,false,false⟩ 1 pattern = decide (d570 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases e <;> cases f <;> cases g <;> rfl
theorem push103_1 : PushBound ⟨66,52,80,80,.south,0,10,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d570 pattern = 1 := of_decide_eq_true (by rw [← guard_push103_1]; exact allowed)
  have checked := c3497 pattern guarded
  change d291 pattern ≤ (0 : Int) + d331 (change pattern 6 10)
  rw [s1355]
  exact checked
theorem guard_push104_0 (pattern : Ten) : pushGuard ⟨80,94,66,66,.north,2,11,false,false⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem push104_0 : PushBound ⟨80,94,66,66,.north,2,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_push104_0]; exact allowed)
  have checked := c3561 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 6)
  rw [s1389]
  exact checked
theorem guard_push104_1 (pattern : Ten) : pushGuard ⟨80,94,66,66,.north,2,11,false,false⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem push104_1 : PushBound ⟨80,94,66,66,.north,2,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_push104_1]; exact allowed)
  have checked := c3657 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 6)
  rw [s1425]
  exact checked
theorem guard_push105_0 (pattern : Ten) : pushGuard ⟨80,66,94,94,.south,0,11,false,false⟩ 0 pattern = decide (d395 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem push105_0 : PushBound ⟨80,66,94,94,.south,0,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d395 pattern = 1 := of_decide_eq_true (by rw [← guard_push105_0]; exact allowed)
  have checked := c1195 pattern guarded
  change d156 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push105_1 (pattern : Ten) : pushGuard ⟨80,66,94,94,.south,0,11,false,false⟩ 1 pattern = decide (d394 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases g <;> rfl
theorem push105_1 : PushBound ⟨80,66,94,94,.south,0,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d394 pattern = 1 := of_decide_eq_true (by rw [← guard_push105_1]; exact allowed)
  have checked := c1203 pattern guarded
  change d331 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push106_0 (pattern : Ten) : pushGuard ⟨86,85,87,87,.east,0,20,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push106_0 : PushBound ⟨86,85,87,87,.east,0,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push106_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push106_1 (pattern : Ten) : pushGuard ⟨86,85,87,87,.east,0,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push106_1 : PushBound ⟨86,85,87,87,.east,0,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push106_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push107_0 (pattern : Ten) : pushGuard ⟨86,87,85,85,.west,20,20,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push107_0 : PushBound ⟨86,87,85,85,.west,20,20,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push107_0]; exact allowed)
  have checked := c3748 pattern guarded
  change d170 pattern ≤ (20 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push107_1 (pattern : Ten) : pushGuard ⟨86,87,85,85,.west,20,20,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push107_1 : PushBound ⟨86,87,85,85,.west,20,20,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push107_1]; exact allowed)
  have checked := c3808 pattern guarded
  change d349 pattern ≤ (20 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push108_0 (pattern : Ten) : pushGuard ⟨87,86,88,88,.east,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push108_0 : PushBound ⟨87,86,88,88,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push108_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push108_1 (pattern : Ten) : pushGuard ⟨87,86,88,88,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push108_1 : PushBound ⟨87,86,88,88,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push108_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push109_0 (pattern : Ten) : pushGuard ⟨87,88,86,86,.west,2,2,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push109_0 : PushBound ⟨87,88,86,86,.west,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push109_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push109_1 (pattern : Ten) : pushGuard ⟨87,88,86,86,.west,2,2,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push109_1 : PushBound ⟨87,88,86,86,.west,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push109_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push110_0 (pattern : Ten) : pushGuard ⟨88,87,89,89,.east,2,22,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push110_0 : PushBound ⟨88,87,89,89,.east,2,22,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push110_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push110_1 (pattern : Ten) : pushGuard ⟨88,87,89,89,.east,2,22,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push110_1 : PushBound ⟨88,87,89,89,.east,2,22,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push110_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push111_0 (pattern : Ten) : pushGuard ⟨88,89,87,87,.west,2,22,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push111_0 : PushBound ⟨88,89,87,87,.west,2,22,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push111_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push111_1 (pattern : Ten) : pushGuard ⟨88,89,87,87,.west,2,22,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push111_1 : PushBound ⟨88,89,87,87,.west,2,22,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push111_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push112_0 (pattern : Ten) : pushGuard ⟨89,88,90,90,.east,21,21,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push112_0 : PushBound ⟨89,88,90,90,.east,21,21,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push112_0]; exact allowed)
  have checked := c3899 pattern guarded
  change d170 pattern ≤ (21 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push112_1 (pattern : Ten) : pushGuard ⟨89,88,90,90,.east,21,21,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push112_1 : PushBound ⟨89,88,90,90,.east,21,21,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push112_1]; exact allowed)
  have checked := c3959 pattern guarded
  change d349 pattern ≤ (21 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push113_0 (pattern : Ten) : pushGuard ⟨89,90,88,88,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push113_0 : PushBound ⟨89,90,88,88,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push113_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push113_1 (pattern : Ten) : pushGuard ⟨89,90,88,88,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push113_1 : PushBound ⟨89,90,88,88,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push113_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push114_0 (pattern : Ten) : pushGuard ⟨151,150,152,152,.east,15,15,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push114_0 : PushBound ⟨151,150,152,152,.east,15,15,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push114_0]; exact allowed)
  have checked := c4050 pattern guarded
  change d170 pattern ≤ (15 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push114_1 (pattern : Ten) : pushGuard ⟨151,150,152,152,.east,15,15,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push114_1 : PushBound ⟨151,150,152,152,.east,15,15,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push114_1]; exact allowed)
  have checked := c4110 pattern guarded
  change d349 pattern ≤ (15 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push115_0 (pattern : Ten) : pushGuard ⟨151,152,150,150,.west,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push115_0 : PushBound ⟨151,152,150,150,.west,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push115_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push115_1 (pattern : Ten) : pushGuard ⟨151,152,150,150,.west,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push115_1 : PushBound ⟨151,152,150,150,.west,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push115_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push116_0 (pattern : Ten) : pushGuard ⟨93,92,94,94,.east,0,11,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push116_0 : PushBound ⟨93,92,94,94,.east,0,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push116_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push116_1 (pattern : Ten) : pushGuard ⟨93,92,94,94,.east,0,11,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push116_1 : PushBound ⟨93,92,94,94,.east,0,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push116_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push117_0 (pattern : Ten) : pushGuard ⟨93,94,92,92,.west,11,11,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push117_0 : PushBound ⟨93,94,92,92,.west,11,11,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push117_0]; exact allowed)
  have checked := c4201 pattern guarded
  change d170 pattern ≤ (11 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push117_1 (pattern : Ten) : pushGuard ⟨93,94,92,92,.west,11,11,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push117_1 : PushBound ⟨93,94,92,92,.west,11,11,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push117_1]; exact allowed)
  have checked := c4261 pattern guarded
  change d349 pattern ≤ (11 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push118_0 (pattern : Ten) : pushGuard ⟨94,108,80,80,.north,2,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push118_0 : PushBound ⟨94,108,80,80,.north,2,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push118_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push118_1 (pattern : Ten) : pushGuard ⟨94,108,80,80,.north,2,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push118_1 : PushBound ⟨94,108,80,80,.north,2,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push118_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push119_0 (pattern : Ten) : pushGuard ⟨94,93,95,95,.east,2,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push119_0 : PushBound ⟨94,93,95,95,.east,2,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push119_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push119_1 (pattern : Ten) : pushGuard ⟨94,93,95,95,.east,2,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push119_1 : PushBound ⟨94,93,95,95,.east,2,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push119_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push120_0 (pattern : Ten) : pushGuard ⟨94,80,108,108,.south,0,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push120_0 : PushBound ⟨94,80,108,108,.south,0,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push120_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push120_1 (pattern : Ten) : pushGuard ⟨94,80,108,108,.south,0,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push120_1 : PushBound ⟨94,80,108,108,.south,0,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push120_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push121_0 (pattern : Ten) : pushGuard ⟨94,95,93,93,.west,2,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push121_0 : PushBound ⟨94,95,93,93,.west,2,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push121_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push121_1 (pattern : Ten) : pushGuard ⟨94,95,93,93,.west,2,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push121_1 : PushBound ⟨94,95,93,93,.west,2,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push121_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push122_0 (pattern : Ten) : pushGuard ⟨95,94,96,96,.east,11,11,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push122_0 : PushBound ⟨95,94,96,96,.east,11,11,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_0]; exact allowed)
  have checked := c4201 pattern guarded
  change d170 pattern ≤ (11 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push122_1 (pattern : Ten) : pushGuard ⟨95,94,96,96,.east,11,11,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push122_1 : PushBound ⟨95,94,96,96,.east,11,11,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push122_1]; exact allowed)
  have checked := c4261 pattern guarded
  change d349 pattern ≤ (11 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push123_0 (pattern : Ten) : pushGuard ⟨95,96,94,94,.west,0,11,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push123_0 : PushBound ⟨95,96,94,94,.west,0,11,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push123_1 (pattern : Ten) : pushGuard ⟨95,96,94,94,.west,0,11,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push123_1 : PushBound ⟨95,96,94,94,.west,0,11,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push123_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push124_0 (pattern : Ten) : pushGuard ⟨100,114,86,86,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push124_0 : PushBound ⟨100,114,86,86,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push124_1 (pattern : Ten) : pushGuard ⟨100,114,86,86,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push124_1 : PushBound ⟨100,114,86,86,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push124_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push125_0 (pattern : Ten) : pushGuard ⟨100,86,114,114,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push125_0 : PushBound ⟨100,86,114,114,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push125_1 (pattern : Ten) : pushGuard ⟨100,86,114,114,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push125_1 : PushBound ⟨100,86,114,114,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push125_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push126_0 (pattern : Ten) : pushGuard ⟨106,120,92,92,.north,15,15,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push126_0 : PushBound ⟨106,120,92,92,.north,15,15,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_0]; exact allowed)
  have checked := c4050 pattern guarded
  change d170 pattern ≤ (15 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push126_1 (pattern : Ten) : pushGuard ⟨106,120,92,92,.north,15,15,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push126_1 : PushBound ⟨106,120,92,92,.north,15,15,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push126_1]; exact allowed)
  have checked := c4110 pattern guarded
  change d349 pattern ≤ (15 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push127_0 (pattern : Ten) : pushGuard ⟨106,92,120,120,.south,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push127_0 : PushBound ⟨106,92,120,120,.south,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push127_1 (pattern : Ten) : pushGuard ⟨106,92,120,120,.south,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push127_1 : PushBound ⟨106,92,120,120,.south,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push127_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push128_0 (pattern : Ten) : pushGuard ⟨107,121,93,93,.north,4,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push128_0 : PushBound ⟨107,121,93,93,.north,4,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_0]; exact allowed)
  have checked := c1648 pattern guarded
  change d170 pattern ≤ (4 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push128_1 (pattern : Ten) : pushGuard ⟨107,121,93,93,.north,4,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push128_1 : PushBound ⟨107,121,93,93,.north,4,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push128_1]; exact allowed)
  have checked := c1649 pattern guarded
  change d349 pattern ≤ (4 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push129_0 (pattern : Ten) : pushGuard ⟨107,106,108,108,.east,2,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push129_0 : PushBound ⟨107,106,108,108,.east,2,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push129_1 (pattern : Ten) : pushGuard ⟨107,106,108,108,.east,2,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push129_1 : PushBound ⟨107,106,108,108,.east,2,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push129_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push130_0 (pattern : Ten) : pushGuard ⟨107,93,121,121,.south,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push130_0 : PushBound ⟨107,93,121,121,.south,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push130_1 (pattern : Ten) : pushGuard ⟨107,93,121,121,.south,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push130_1 : PushBound ⟨107,93,121,121,.south,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push130_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push131_0 (pattern : Ten) : pushGuard ⟨107,108,106,106,.west,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push131_0 : PushBound ⟨107,108,106,106,.west,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push131_1 (pattern : Ten) : pushGuard ⟨107,108,106,106,.west,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push131_1 : PushBound ⟨107,108,106,106,.west,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push131_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push132_0 (pattern : Ten) : pushGuard ⟨108,122,94,94,.north,2,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push132_0 : PushBound ⟨108,122,94,94,.north,2,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push132_1 (pattern : Ten) : pushGuard ⟨108,122,94,94,.north,2,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push132_1 : PushBound ⟨108,122,94,94,.north,2,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push132_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push133_0 (pattern : Ten) : pushGuard ⟨108,107,109,109,.east,2,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push133_0 : PushBound ⟨108,107,109,109,.east,2,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push133_1 (pattern : Ten) : pushGuard ⟨108,107,109,109,.east,2,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push133_1 : PushBound ⟨108,107,109,109,.east,2,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push134_0 (pattern : Ten) : pushGuard ⟨108,94,122,122,.south,0,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push134_0 : PushBound ⟨108,94,122,122,.south,0,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push134_1 (pattern : Ten) : pushGuard ⟨108,94,122,122,.south,0,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push134_1 : PushBound ⟨108,94,122,122,.south,0,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push135_0 (pattern : Ten) : pushGuard ⟨108,109,107,107,.west,0,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push135_0 : PushBound ⟨108,109,107,107,.west,0,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push135_1 (pattern : Ten) : pushGuard ⟨108,109,107,107,.west,0,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push135_1 : PushBound ⟨108,109,107,107,.west,0,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
end NetHack.Sokoban41
