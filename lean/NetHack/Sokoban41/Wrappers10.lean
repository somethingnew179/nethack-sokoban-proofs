/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers09
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_walk350_0 (pattern : Ten) : walkGuard ⟨157,143,.north⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk350_0 : WalkBound ⟨157,143,.north⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk350_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk350_1 (pattern : Ten) : walkGuard ⟨157,143,.north⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk350_1 : WalkBound ⟨157,143,.north⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk350_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk351_0 (pattern : Ten) : walkGuard ⟨157,156,.west⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk351_0 : WalkBound ⟨157,156,.west⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk351_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk351_1 (pattern : Ten) : walkGuard ⟨157,156,.west⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk351_1 : WalkBound ⟨157,156,.west⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk351_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk352_0 (pattern : Ten) : walkGuard ⟨157,144,.northEast⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk352_0 : WalkBound ⟨157,144,.northEast⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk352_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk352_1 (pattern : Ten) : walkGuard ⟨157,144,.northEast⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk352_1 : WalkBound ⟨157,144,.northEast⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk352_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk353_0 (pattern : Ten) : walkGuard ⟨157,142,.northWest⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk353_0 : WalkBound ⟨157,142,.northWest⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_walk353_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ d170 pattern
  simpa only [Int.zero_add] using checked
theorem guard_walk353_1 (pattern : Ten) : walkGuard ⟨157,142,.northWest⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem walk353_1 : WalkBound ⟨157,142,.northWest⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_walk353_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ d349 pattern
  simpa only [Int.zero_add] using checked
theorem guard_push0_0 (pattern : Ten) : pushGuard ⟨128,142,114,114,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push0_0 : PushBound ⟨128,142,114,114,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push0_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push0_1 (pattern : Ten) : pushGuard ⟨128,142,114,114,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push0_1 : PushBound ⟨128,142,114,114,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push0_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push1_0 (pattern : Ten) : pushGuard ⟨128,114,142,142,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push1_0 : PushBound ⟨128,114,142,142,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push1_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push1_1 (pattern : Ten) : pushGuard ⟨128,114,142,142,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push1_1 : PushBound ⟨128,114,142,142,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push1_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push2_0 (pattern : Ten) : pushGuard ⟨134,148,120,120,.north,2,17,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push2_0 : PushBound ⟨134,148,120,120,.north,2,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push2_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push2_1 (pattern : Ten) : pushGuard ⟨134,148,120,120,.north,2,17,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push2_1 : PushBound ⟨134,148,120,120,.north,2,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push2_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push3_0 (pattern : Ten) : pushGuard ⟨134,120,148,148,.south,0,17,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push3_0 : PushBound ⟨134,120,148,148,.south,0,17,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push3_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push3_1 (pattern : Ten) : pushGuard ⟨134,120,148,148,.south,0,17,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push3_1 : PushBound ⟨134,120,148,148,.south,0,17,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push3_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push4_0 (pattern : Ten) : pushGuard ⟨135,149,121,121,.north,2,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push4_0 : PushBound ⟨135,149,121,121,.north,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push4_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push4_1 (pattern : Ten) : pushGuard ⟨135,149,121,121,.north,2,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push4_1 : PushBound ⟨135,149,121,121,.north,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push4_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push5_0 (pattern : Ten) : pushGuard ⟨135,134,136,136,.east,2,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push5_0 : PushBound ⟨135,134,136,136,.east,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push5_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push5_1 (pattern : Ten) : pushGuard ⟨135,134,136,136,.east,2,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push5_1 : PushBound ⟨135,134,136,136,.east,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push5_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push6_0 (pattern : Ten) : pushGuard ⟨135,121,149,149,.south,0,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push6_0 : PushBound ⟨135,121,149,149,.south,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push6_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push6_1 (pattern : Ten) : pushGuard ⟨135,121,149,149,.south,0,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push6_1 : PushBound ⟨135,121,149,149,.south,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push6_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push7_0 (pattern : Ten) : pushGuard ⟨135,136,134,134,.west,0,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push7_0 : PushBound ⟨135,136,134,134,.west,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push7_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push7_1 (pattern : Ten) : pushGuard ⟨135,136,134,134,.west,0,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push7_1 : PushBound ⟨135,136,134,134,.west,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push7_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push8_0 (pattern : Ten) : pushGuard ⟨136,150,122,122,.north,2,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push8_0 : PushBound ⟨136,150,122,122,.north,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push8_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push8_1 (pattern : Ten) : pushGuard ⟨136,150,122,122,.north,2,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push8_1 : PushBound ⟨136,150,122,122,.north,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push8_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push9_0 (pattern : Ten) : pushGuard ⟨136,135,137,137,.east,2,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push9_0 : PushBound ⟨136,135,137,137,.east,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push9_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push9_1 (pattern : Ten) : pushGuard ⟨136,135,137,137,.east,2,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push9_1 : PushBound ⟨136,135,137,137,.east,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push9_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push10_0 (pattern : Ten) : pushGuard ⟨136,122,150,150,.south,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push10_0 : PushBound ⟨136,122,150,150,.south,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push10_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push10_1 (pattern : Ten) : pushGuard ⟨136,122,150,150,.south,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push10_1 : PushBound ⟨136,122,150,150,.south,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push10_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push11_0 (pattern : Ten) : pushGuard ⟨136,137,135,135,.west,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push11_0 : PushBound ⟨136,137,135,135,.west,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push11_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push11_1 (pattern : Ten) : pushGuard ⟨136,137,135,135,.west,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push11_1 : PushBound ⟨136,137,135,135,.west,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push11_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push12_0 (pattern : Ten) : pushGuard ⟨137,151,123,123,.north,2,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push12_0 : PushBound ⟨137,151,123,123,.north,2,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push12_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push12_1 (pattern : Ten) : pushGuard ⟨137,151,123,123,.north,2,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push12_1 : PushBound ⟨137,151,123,123,.north,2,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push12_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push13_0 (pattern : Ten) : pushGuard ⟨137,136,138,138,.east,14,14,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push13_0 : PushBound ⟨137,136,138,138,.east,14,14,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push13_0]; exact allowed)
  have checked := c1432 pattern guarded
  change d170 pattern ≤ (14 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push13_1 (pattern : Ten) : pushGuard ⟨137,136,138,138,.east,14,14,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push13_1 : PushBound ⟨137,136,138,138,.east,14,14,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push13_1]; exact allowed)
  have checked := c1492 pattern guarded
  change d349 pattern ≤ (14 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push14_0 (pattern : Ten) : pushGuard ⟨137,123,151,151,.south,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push14_0 : PushBound ⟨137,123,151,151,.south,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push14_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push14_1 (pattern : Ten) : pushGuard ⟨137,123,151,151,.south,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push14_1 : PushBound ⟨137,123,151,151,.south,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push14_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push15_0 (pattern : Ten) : pushGuard ⟨137,138,136,136,.west,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push15_0 : PushBound ⟨137,138,136,136,.west,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push15_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push15_1 (pattern : Ten) : pushGuard ⟨137,138,136,136,.west,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push15_1 : PushBound ⟨137,138,136,136,.west,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push15_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push16_0 : PushBound ⟨138,152,124,124,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push16_1 (pattern : Ten) : pushGuard ⟨138,152,124,124,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push16_1 : PushBound ⟨138,152,124,124,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push16_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push17_0 : PushBound ⟨138,124,152,152,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push17_1 (pattern : Ten) : pushGuard ⟨138,124,152,152,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push17_1 : PushBound ⟨138,124,152,152,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push17_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push18_0 (pattern : Ten) : pushGuard ⟨142,156,128,142,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push18_0 : PushBound ⟨142,156,128,142,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push18_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push18_1 (pattern : Ten) : pushGuard ⟨142,156,128,142,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push18_1 : PushBound ⟨142,156,128,142,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push18_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push19_0 (pattern : Ten) : pushGuard ⟨142,156,128,128,.north,1,19,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push19_0 : PushBound ⟨142,156,128,128,.north,1,19,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push19_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push19_1 (pattern : Ten) : pushGuard ⟨142,156,128,128,.north,1,19,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push19_1 : PushBound ⟨142,156,128,128,.north,1,19,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push19_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push20_0 (pattern : Ten) : pushGuard ⟨142,156,128,114,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push20_0 : PushBound ⟨142,156,128,114,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push20_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push20_1 (pattern : Ten) : pushGuard ⟨142,156,128,114,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push20_1 : PushBound ⟨142,156,128,114,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push20_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push21_0 (pattern : Ten) : pushGuard ⟨142,156,128,100,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push21_0 : PushBound ⟨142,156,128,100,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push21_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push21_1 (pattern : Ten) : pushGuard ⟨142,156,128,100,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push21_1 : PushBound ⟨142,156,128,100,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push21_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push22_0 (pattern : Ten) : pushGuard ⟨142,156,128,86,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push22_0 : PushBound ⟨142,156,128,86,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push22_1 (pattern : Ten) : pushGuard ⟨142,156,128,86,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push22_1 : PushBound ⟨142,156,128,86,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push22_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push23_0 (pattern : Ten) : pushGuard ⟨142,128,156,156,.south,19,19,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push23_0 : PushBound ⟨142,128,156,156,.south,19,19,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_0]; exact allowed)
  have checked := c1584 pattern guarded
  change d170 pattern ≤ (19 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push23_1 (pattern : Ten) : pushGuard ⟨142,128,156,156,.south,19,19,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push23_1 : PushBound ⟨142,128,156,156,.south,19,19,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push23_1]; exact allowed)
  have checked := c1644 pattern guarded
  change d349 pattern ≤ (19 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem push24_0 : PushBound ⟨16,15,17,17,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push24_1 (pattern : Ten) : pushGuard ⟨16,15,17,17,.east,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push24_1 : PushBound ⟨16,15,17,17,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push24_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem push25_0 : PushBound ⟨16,17,15,15,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push25_1 (pattern : Ten) : pushGuard ⟨16,17,15,15,.west,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push25_1 : PushBound ⟨16,17,15,15,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push25_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem push26_0 : PushBound ⟨17,16,18,18,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push26_1 (pattern : Ten) : pushGuard ⟨17,16,18,18,.east,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push26_1 : PushBound ⟨17,16,18,18,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push26_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem push27_0 : PushBound ⟨17,18,16,16,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push27_1 (pattern : Ten) : pushGuard ⟨17,18,16,16,.west,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push27_1 : PushBound ⟨17,18,16,16,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push27_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push28_0 (pattern : Ten) : pushGuard ⟨143,142,144,144,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push28_0 : PushBound ⟨143,142,144,144,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push28_1 (pattern : Ten) : pushGuard ⟨143,142,144,144,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push28_1 : PushBound ⟨143,142,144,144,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push28_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push29_0 (pattern : Ten) : pushGuard ⟨143,144,142,142,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push29_0 : PushBound ⟨143,144,142,142,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push29_1 (pattern : Ten) : pushGuard ⟨143,144,142,142,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push29_1 : PushBound ⟨143,144,142,142,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push29_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push30_0 (pattern : Ten) : pushGuard ⟨144,143,145,145,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push30_0 : PushBound ⟨144,143,145,145,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push30_1 (pattern : Ten) : pushGuard ⟨144,143,145,145,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push30_1 : PushBound ⟨144,143,145,145,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push30_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
end NetHack.Sokoban41
