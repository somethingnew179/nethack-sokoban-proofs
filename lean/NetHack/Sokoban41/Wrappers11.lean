/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers10
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_push31_0 (pattern : Ten) : pushGuard ⟨144,145,143,143,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push31_0 : PushBound ⟨144,145,143,143,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push31_1 (pattern : Ten) : pushGuard ⟨144,145,143,143,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push31_1 : PushBound ⟨144,145,143,143,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push31_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push32_0 (pattern : Ten) : pushGuard ⟨145,144,146,146,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push32_0 : PushBound ⟨145,144,146,146,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push32_1 (pattern : Ten) : pushGuard ⟨145,144,146,146,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push32_1 : PushBound ⟨145,144,146,146,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push32_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push33_0 (pattern : Ten) : pushGuard ⟨145,146,144,144,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push33_0 : PushBound ⟨145,146,144,144,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push33_1 (pattern : Ten) : pushGuard ⟨145,146,144,144,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push33_1 : PushBound ⟨145,146,144,144,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push33_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push34_0 (pattern : Ten) : pushGuard ⟨146,145,147,146,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push34_0 : PushBound ⟨146,145,147,146,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push34_1 (pattern : Ten) : pushGuard ⟨146,145,147,146,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push34_1 : PushBound ⟨146,145,147,146,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push34_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push35_0 (pattern : Ten) : pushGuard ⟨146,145,147,147,.east,2,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push35_0 : PushBound ⟨146,145,147,147,.east,2,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push35_1 (pattern : Ten) : pushGuard ⟨146,145,147,147,.east,2,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push35_1 : PushBound ⟨146,145,147,147,.east,2,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push35_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push36_0 (pattern : Ten) : pushGuard ⟨146,145,147,148,.east,2,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push36_0 : PushBound ⟨146,145,147,148,.east,2,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push36_1 (pattern : Ten) : pushGuard ⟨146,145,147,148,.east,2,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push36_1 : PushBound ⟨146,145,147,148,.east,2,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push36_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push37_0 (pattern : Ten) : pushGuard ⟨146,145,147,149,.east,3,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push37_0 : PushBound ⟨146,145,147,149,.east,3,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_0]; exact allowed)
  have checked := c1646 pattern guarded
  change d170 pattern ≤ (3 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push37_1 (pattern : Ten) : pushGuard ⟨146,145,147,149,.east,3,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push37_1 : PushBound ⟨146,145,147,149,.east,3,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push37_1]; exact allowed)
  have checked := c1647 pattern guarded
  change d349 pattern ≤ (3 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push38_0 (pattern : Ten) : pushGuard ⟨146,145,147,150,.east,4,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push38_0 : PushBound ⟨146,145,147,150,.east,4,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_0]; exact allowed)
  have checked := c1648 pattern guarded
  change d170 pattern ≤ (4 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push38_1 (pattern : Ten) : pushGuard ⟨146,145,147,150,.east,4,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push38_1 : PushBound ⟨146,145,147,150,.east,4,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push38_1]; exact allowed)
  have checked := c1649 pattern guarded
  change d349 pattern ≤ (4 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push39_0 (pattern : Ten) : pushGuard ⟨146,145,147,151,.east,5,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push39_0 : PushBound ⟨146,145,147,151,.east,5,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_0]; exact allowed)
  have checked := c1650 pattern guarded
  change d170 pattern ≤ (5 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push39_1 (pattern : Ten) : pushGuard ⟨146,145,147,151,.east,5,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push39_1 : PushBound ⟨146,145,147,151,.east,5,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push39_1]; exact allowed)
  have checked := c1651 pattern guarded
  change d349 pattern ≤ (5 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push40_0 (pattern : Ten) : pushGuard ⟨146,145,147,152,.east,19,19,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push40_0 : PushBound ⟨146,145,147,152,.east,19,19,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push40_0]; exact allowed)
  have checked := c1584 pattern guarded
  change d170 pattern ≤ (19 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push40_1 (pattern : Ten) : pushGuard ⟨146,145,147,152,.east,19,19,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push40_1 : PushBound ⟨146,145,147,152,.east,19,19,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push40_1]; exact allowed)
  have checked := c1644 pattern guarded
  change d349 pattern ≤ (19 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push41_0 (pattern : Ten) : pushGuard ⟨146,147,145,145,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push41_0 : PushBound ⟨146,147,145,145,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push41_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push41_1 (pattern : Ten) : pushGuard ⟨146,147,145,145,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push41_1 : PushBound ⟨146,147,145,145,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push41_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push42_0 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push42_1 (pattern : Ten) : pushGuard ⟨24,23,25,25,.east,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push42_1 : PushBound ⟨24,23,25,25,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push42_1]; exact allowed)
  have checked := c1652 pattern guarded
  change d220 pattern ≤ (1 : Int) + d220 (change pattern 10 10)
  rw [s130]
  exact checked
theorem push43_0 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push43_1 (pattern : Ten) : pushGuard ⟨24,25,23,23,.west,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push43_1 : PushBound ⟨24,25,23,23,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push43_1]; exact allowed)
  have checked := c1652 pattern guarded
  change d220 pattern ≤ (1 : Int) + d220 (change pattern 10 10)
  rw [s130]
  exact checked
theorem guard_push44_0 (pattern : Ten) : pushGuard ⟨147,146,148,148,.east,1,18,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push44_0 : PushBound ⟨147,146,148,148,.east,1,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push44_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push44_1 (pattern : Ten) : pushGuard ⟨147,146,148,148,.east,1,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push44_1 : PushBound ⟨147,146,148,148,.east,1,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push44_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push45_0 (pattern : Ten) : pushGuard ⟨147,148,146,146,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push45_0 : PushBound ⟨147,148,146,146,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push45_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push45_1 (pattern : Ten) : pushGuard ⟨147,148,146,146,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push45_1 : PushBound ⟨147,148,146,146,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push45_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push46_0 (pattern : Ten) : pushGuard ⟨148,147,149,149,.east,2,18,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push46_0 : PushBound ⟨148,147,149,149,.east,2,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push46_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push46_1 (pattern : Ten) : pushGuard ⟨148,147,149,149,.east,2,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push46_1 : PushBound ⟨148,147,149,149,.east,2,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push46_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push47_0 (pattern : Ten) : pushGuard ⟨148,149,147,148,.west,1,18,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push47_0 : PushBound ⟨148,149,147,148,.west,1,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push47_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push47_1 (pattern : Ten) : pushGuard ⟨148,149,147,148,.west,1,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push47_1 : PushBound ⟨148,149,147,148,.west,1,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push47_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push48_0 (pattern : Ten) : pushGuard ⟨148,149,147,147,.west,1,18,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push48_0 : PushBound ⟨148,149,147,147,.west,1,18,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push48_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push48_1 (pattern : Ten) : pushGuard ⟨148,149,147,147,.west,1,18,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push48_1 : PushBound ⟨148,149,147,147,.west,1,18,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push48_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push49_0 (pattern : Ten) : pushGuard ⟨148,149,147,146,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push49_0 : PushBound ⟨148,149,147,146,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push49_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push49_1 (pattern : Ten) : pushGuard ⟨148,149,147,146,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push49_1 : PushBound ⟨148,149,147,146,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push49_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push50_0 (pattern : Ten) : pushGuard ⟨148,149,147,145,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push50_0 : PushBound ⟨148,149,147,145,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push50_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push50_1 (pattern : Ten) : pushGuard ⟨148,149,147,145,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push50_1 : PushBound ⟨148,149,147,145,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push50_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push51_0 (pattern : Ten) : pushGuard ⟨148,149,147,144,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push51_0 : PushBound ⟨148,149,147,144,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push51_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push51_1 (pattern : Ten) : pushGuard ⟨148,149,147,144,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push51_1 : PushBound ⟨148,149,147,144,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push51_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push52_0 (pattern : Ten) : pushGuard ⟨148,149,147,143,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push52_0 : PushBound ⟨148,149,147,143,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push52_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push52_1 (pattern : Ten) : pushGuard ⟨148,149,147,143,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push52_1 : PushBound ⟨148,149,147,143,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push52_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push53_0 (pattern : Ten) : pushGuard ⟨148,149,147,142,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push53_0 : PushBound ⟨148,149,147,142,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push53_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push53_1 (pattern : Ten) : pushGuard ⟨148,149,147,142,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push53_1 : PushBound ⟨148,149,147,142,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push53_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push54_0 (pattern : Ten) : pushGuard ⟨149,148,150,150,.east,2,17,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push54_0 : PushBound ⟨149,148,150,150,.east,2,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push54_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push54_1 (pattern : Ten) : pushGuard ⟨149,148,150,150,.east,2,17,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push54_1 : PushBound ⟨149,148,150,150,.east,2,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push54_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push55_0 (pattern : Ten) : pushGuard ⟨149,150,148,148,.west,0,17,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push55_0 : PushBound ⟨149,150,148,148,.west,0,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push55_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push55_1 (pattern : Ten) : pushGuard ⟨149,150,148,148,.west,0,17,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push55_1 : PushBound ⟨149,150,148,148,.west,0,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push55_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push56_0 : PushBound ⟨29,43,15,15,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push56_1 (pattern : Ten) : pushGuard ⟨29,43,15,15,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push56_1 : PushBound ⟨29,43,15,15,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push56_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem push57_0 : PushBound ⟨29,15,43,43,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push57_1 (pattern : Ten) : pushGuard ⟨29,15,43,43,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push57_1 : PushBound ⟨29,15,43,43,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push57_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push58_0 (pattern : Ten) : pushGuard ⟨30,44,16,16,.north,1,1,false,true⟩ 0 pattern = decide (d407 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push58_0 : PushBound ⟨30,44,16,16,.north,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d407 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_0]; exact allowed)
  have checked := c1678 pattern guarded
  change d37 pattern ≤ (1 : Int) + d234 (change pattern 0 10)
  rw [s156]
  exact checked
theorem guard_push58_1 (pattern : Ten) : pushGuard ⟨30,44,16,16,.north,1,1,false,true⟩ 1 pattern = decide (d406 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push58_1 : PushBound ⟨30,44,16,16,.north,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d406 pattern = 1 := of_decide_eq_true (by rw [← guard_push58_1]; exact allowed)
  have checked := c1709 pattern guarded
  change d248 pattern ≤ (1 : Int) + d10 (change pattern 0 10)
  rw [s135]
  exact checked
theorem guard_push59_0 (pattern : Ten) : pushGuard ⟨30,29,31,31,.east,1,1,false,false⟩ 0 pattern = decide (d292 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push59_0 : PushBound ⟨30,29,31,31,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d292 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_0]; exact allowed)
  have checked := c1735 pattern guarded
  change d37 pattern ≤ (1 : Int) + d81 (change pattern 0 10)
  rw [s174]
  exact checked
theorem guard_push59_1 (pattern : Ten) : pushGuard ⟨30,29,31,31,.east,1,1,false,false⟩ 1 pattern = decide (d171 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push59_1 : PushBound ⟨30,29,31,31,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d171 pattern = 1 := of_decide_eq_true (by rw [← guard_push59_1]; exact allowed)
  have checked := c1762 pattern guarded
  change d192 pattern ≤ (1 : Int) + d234 (change pattern 0 10)
  rw [s156]
  exact checked
theorem guard_push60_0 (pattern : Ten) : pushGuard ⟨30,16,44,44,.south,1,1,false,false⟩ 0 pattern = decide (d407 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push60_0 : PushBound ⟨30,16,44,44,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d407 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_0]; exact allowed)
  have checked := c1780 pattern guarded
  change d37 pattern ≤ (1 : Int) + d81 (change pattern 0 1)
  rw [s204]
  exact checked
theorem guard_push60_1 (pattern : Ten) : pushGuard ⟨30,16,44,44,.south,1,1,false,false⟩ 1 pattern = decide (d406 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push60_1 : PushBound ⟨30,16,44,44,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d406 pattern = 1 := of_decide_eq_true (by rw [← guard_push60_1]; exact allowed)
  have checked := c1804 pattern guarded
  change d192 pattern ≤ (1 : Int) + d234 (change pattern 0 1)
  rw [s218]
  exact checked
theorem guard_push61_0 (pattern : Ten) : pushGuard ⟨30,31,29,29,.west,1,1,false,true⟩ 0 pattern = decide (d292 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push61_0 : PushBound ⟨30,31,29,29,.west,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d292 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_0]; exact allowed)
  have checked := c1822 pattern guarded
  change d37 pattern ≤ (1 : Int) + d234 (change pattern 0 10)
  rw [s156]
  exact checked
theorem guard_push61_1 (pattern : Ten) : pushGuard ⟨30,31,29,29,.west,1,1,false,true⟩ 1 pattern = decide (d171 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push61_1 : PushBound ⟨30,31,29,29,.west,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d171 pattern = 1 := of_decide_eq_true (by rw [← guard_push61_1]; exact allowed)
  have checked := c1846 pattern guarded
  change d192 pattern ≤ (1 : Int) + d10 (change pattern 0 10)
  rw [s135]
  exact checked
theorem guard_push62_0 (pattern : Ten) : pushGuard ⟨31,45,17,17,.north,1,1,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push62_0 : PushBound ⟨31,45,17,17,.north,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_0]; exact allowed)
  have checked := c1886 pattern guarded
  change d37 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push62_1 (pattern : Ten) : pushGuard ⟨31,45,17,17,.north,1,1,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push62_1 : PushBound ⟨31,45,17,17,.north,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push62_1]; exact allowed)
  have checked := c1910 pattern guarded
  change d192 pattern ≤ (1 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push63_0 (pattern : Ten) : pushGuard ⟨31,30,32,32,.east,0,1,false,false⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push63_0 : PushBound ⟨31,30,32,32,.east,0,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_0]; exact allowed)
  have checked := c127 pattern guarded
  change d81 pattern ≤ (0 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push63_1 (pattern : Ten) : pushGuard ⟨31,30,32,32,.east,0,1,false,false⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push63_1 : PushBound ⟨31,30,32,32,.east,0,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_push63_1]; exact allowed)
  have checked := c155 pattern guarded
  change d234 pattern ≤ (0 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push64_0 (pattern : Ten) : pushGuard ⟨31,17,45,45,.south,0,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push64_0 : PushBound ⟨31,17,45,45,.south,0,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push64_1 (pattern : Ten) : pushGuard ⟨31,17,45,45,.south,0,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push64_1 : PushBound ⟨31,17,45,45,.south,0,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push64_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ (0 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push65_0 (pattern : Ten) : pushGuard ⟨31,32,30,30,.west,1,1,false,false⟩ 0 pattern = decide (d352 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push65_0 : PushBound ⟨31,32,30,30,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d352 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_0]; exact allowed)
  have checked := c1934 pattern guarded
  change d37 pattern ≤ (1 : Int) + d37 (change pattern 10 0)
  rw [s273]
  exact checked
theorem guard_push65_1 (pattern : Ten) : pushGuard ⟨31,32,30,30,.west,1,1,false,false⟩ 1 pattern = decide (d351 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases f <;> rfl
theorem push65_1 : PushBound ⟨31,32,30,30,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d351 pattern = 1 := of_decide_eq_true (by rw [← guard_push65_1]; exact allowed)
  have checked := c1959 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 0)
  rw [s297]
  exact checked
end NetHack.Sokoban41
