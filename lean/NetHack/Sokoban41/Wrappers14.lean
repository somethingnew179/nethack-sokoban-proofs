/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers13
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_push136_0 (pattern : Ten) : pushGuard ⟨109,123,95,95,.north,2,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push136_0 : PushBound ⟨109,123,95,95,.north,2,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push136_1 (pattern : Ten) : pushGuard ⟨109,123,95,95,.north,2,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push136_1 : PushBound ⟨109,123,95,95,.north,2,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push137_0 (pattern : Ten) : pushGuard ⟨109,108,110,110,.east,12,12,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push137_0 : PushBound ⟨109,108,110,110,.east,12,12,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_0]; exact allowed)
  have checked := c4352 pattern guarded
  change d170 pattern ≤ (12 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push137_1 (pattern : Ten) : pushGuard ⟨109,108,110,110,.east,12,12,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push137_1 : PushBound ⟨109,108,110,110,.east,12,12,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_1]; exact allowed)
  have checked := c4412 pattern guarded
  change d349 pattern ≤ (12 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push138_0 (pattern : Ten) : pushGuard ⟨109,95,123,123,.south,0,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push138_0 : PushBound ⟨109,95,123,123,.south,0,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push138_1 (pattern : Ten) : pushGuard ⟨109,95,123,123,.south,0,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push138_1 : PushBound ⟨109,95,123,123,.south,0,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push139_0 (pattern : Ten) : pushGuard ⟨109,110,108,108,.west,0,12,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push139_0 : PushBound ⟨109,110,108,108,.west,0,12,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push139_1 (pattern : Ten) : pushGuard ⟨109,110,108,108,.west,0,12,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push139_1 : PushBound ⟨109,110,108,108,.west,0,12,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push140_0 : PushBound ⟨110,124,96,96,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push140_1 (pattern : Ten) : pushGuard ⟨110,124,96,96,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push140_1 : PushBound ⟨110,124,96,96,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push140_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push141_0 : PushBound ⟨110,96,124,124,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push141_1 (pattern : Ten) : pushGuard ⟨110,96,124,124,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push141_1 : PushBound ⟨110,96,124,124,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push141_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push142_0 (pattern : Ten) : pushGuard ⟨114,128,100,100,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push142_0 : PushBound ⟨114,128,100,100,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push142_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push142_1 (pattern : Ten) : pushGuard ⟨114,128,100,100,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push142_1 : PushBound ⟨114,128,100,100,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push142_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push143_0 (pattern : Ten) : pushGuard ⟨114,100,128,114,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push143_0 : PushBound ⟨114,100,128,114,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push143_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push143_1 (pattern : Ten) : pushGuard ⟨114,100,128,114,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push143_1 : PushBound ⟨114,100,128,114,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push143_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push144_0 (pattern : Ten) : pushGuard ⟨114,100,128,128,.south,2,20,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push144_0 : PushBound ⟨114,100,128,128,.south,2,20,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push144_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push144_1 (pattern : Ten) : pushGuard ⟨114,100,128,128,.south,2,20,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push144_1 : PushBound ⟨114,100,128,128,.south,2,20,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push144_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push145_0 (pattern : Ten) : pushGuard ⟨114,100,128,142,.south,2,2,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push145_0 : PushBound ⟨114,100,128,142,.south,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push145_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push145_1 (pattern : Ten) : pushGuard ⟨114,100,128,142,.south,2,2,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push145_1 : PushBound ⟨114,100,128,142,.south,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push145_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push146_0 (pattern : Ten) : pushGuard ⟨114,100,128,156,.south,20,20,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push146_0 : PushBound ⟨114,100,128,156,.south,20,20,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push146_0]; exact allowed)
  have checked := c3748 pattern guarded
  change d170 pattern ≤ (20 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push146_1 (pattern : Ten) : pushGuard ⟨114,100,128,156,.south,20,20,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push146_1 : PushBound ⟨114,100,128,156,.south,20,20,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push146_1]; exact allowed)
  have checked := c3808 pattern guarded
  change d349 pattern ≤ (20 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push147_0 (pattern : Ten) : pushGuard ⟨150,149,151,151,.east,2,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push147_0 : PushBound ⟨150,149,151,151,.east,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push147_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push147_1 (pattern : Ten) : pushGuard ⟨150,149,151,151,.east,2,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push147_1 : PushBound ⟨150,149,151,151,.east,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push147_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push148_0 (pattern : Ten) : pushGuard ⟨150,151,149,149,.west,0,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push148_0 : PushBound ⟨150,151,149,149,.west,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push148_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push148_1 (pattern : Ten) : pushGuard ⟨150,151,149,149,.west,0,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push148_1 : PushBound ⟨150,151,149,149,.west,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push148_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push149_0 (pattern : Ten) : pushGuard ⟨120,134,106,106,.north,2,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push149_0 : PushBound ⟨120,134,106,106,.north,2,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push149_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push149_1 (pattern : Ten) : pushGuard ⟨120,134,106,106,.north,2,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push149_1 : PushBound ⟨120,134,106,106,.north,2,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push149_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push150_0 (pattern : Ten) : pushGuard ⟨120,106,134,134,.south,0,16,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push150_0 : PushBound ⟨120,106,134,134,.south,0,16,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push150_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push150_1 (pattern : Ten) : pushGuard ⟨120,106,134,134,.south,0,16,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push150_1 : PushBound ⟨120,106,134,134,.south,0,16,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push150_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push151_0 (pattern : Ten) : pushGuard ⟨121,135,107,107,.north,2,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push151_0 : PushBound ⟨121,135,107,107,.north,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push151_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push151_1 (pattern : Ten) : pushGuard ⟨121,135,107,107,.north,2,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push151_1 : PushBound ⟨121,135,107,107,.north,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push151_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push152_0 (pattern : Ten) : pushGuard ⟨121,120,122,122,.east,2,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push152_0 : PushBound ⟨121,120,122,122,.east,2,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push152_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push152_1 (pattern : Ten) : pushGuard ⟨121,120,122,122,.east,2,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push152_1 : PushBound ⟨121,120,122,122,.east,2,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push152_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push153_0 (pattern : Ten) : pushGuard ⟨121,107,135,135,.south,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push153_0 : PushBound ⟨121,107,135,135,.south,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push153_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push153_1 (pattern : Ten) : pushGuard ⟨121,107,135,135,.south,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push153_1 : PushBound ⟨121,107,135,135,.south,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push153_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push154_0 (pattern : Ten) : pushGuard ⟨121,122,120,120,.west,0,15,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push154_0 : PushBound ⟨121,122,120,120,.west,0,15,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push154_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push154_1 (pattern : Ten) : pushGuard ⟨121,122,120,120,.west,0,15,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push154_1 : PushBound ⟨121,122,120,120,.west,0,15,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push154_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push155_0 (pattern : Ten) : pushGuard ⟨122,136,108,108,.north,2,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push155_0 : PushBound ⟨122,136,108,108,.north,2,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push155_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push155_1 (pattern : Ten) : pushGuard ⟨122,136,108,108,.north,2,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push155_1 : PushBound ⟨122,136,108,108,.north,2,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push155_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push156_0 (pattern : Ten) : pushGuard ⟨122,121,123,123,.east,2,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push156_0 : PushBound ⟨122,121,123,123,.east,2,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push156_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push156_1 (pattern : Ten) : pushGuard ⟨122,121,123,123,.east,2,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push156_1 : PushBound ⟨122,121,123,123,.east,2,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push156_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push157_0 (pattern : Ten) : pushGuard ⟨122,108,136,136,.south,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push157_0 : PushBound ⟨122,108,136,136,.south,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push157_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push157_1 (pattern : Ten) : pushGuard ⟨122,108,136,136,.south,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push157_1 : PushBound ⟨122,108,136,136,.south,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push157_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push158_0 (pattern : Ten) : pushGuard ⟨122,123,121,121,.west,0,14,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push158_0 : PushBound ⟨122,123,121,121,.west,0,14,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push158_1 (pattern : Ten) : pushGuard ⟨122,123,121,121,.west,0,14,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push158_1 : PushBound ⟨122,123,121,121,.west,0,14,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push158_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push159_0 (pattern : Ten) : pushGuard ⟨123,137,109,109,.north,2,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push159_0 : PushBound ⟨123,137,109,109,.north,2,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push159_1 (pattern : Ten) : pushGuard ⟨123,137,109,109,.north,2,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push159_1 : PushBound ⟨123,137,109,109,.north,2,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push159_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push160_0 (pattern : Ten) : pushGuard ⟨123,122,124,124,.east,13,13,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push160_0 : PushBound ⟨123,122,124,124,.east,13,13,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_0]; exact allowed)
  have checked := c4503 pattern guarded
  change d170 pattern ≤ (13 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push160_1 (pattern : Ten) : pushGuard ⟨123,122,124,124,.east,13,13,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push160_1 : PushBound ⟨123,122,124,124,.east,13,13,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push160_1]; exact allowed)
  have checked := c4563 pattern guarded
  change d349 pattern ≤ (13 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push161_0 (pattern : Ten) : pushGuard ⟨123,109,137,137,.south,0,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push161_0 : PushBound ⟨123,109,137,137,.south,0,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push161_1 (pattern : Ten) : pushGuard ⟨123,109,137,137,.south,0,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push161_1 : PushBound ⟨123,109,137,137,.south,0,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push161_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_push162_0 (pattern : Ten) : pushGuard ⟨123,124,122,122,.west,0,13,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push162_0 : PushBound ⟨123,124,122,122,.west,0,13,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_push162_1 (pattern : Ten) : pushGuard ⟨123,124,122,122,.west,0,13,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push162_1 : PushBound ⟨123,124,122,122,.west,0,13,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push162_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push163_0 : PushBound ⟨124,138,110,110,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push163_1 (pattern : Ten) : pushGuard ⟨124,138,110,110,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push163_1 : PushBound ⟨124,138,110,110,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push163_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem push164_0 : PushBound ⟨124,110,138,138,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push164_1 (pattern : Ten) : pushGuard ⟨124,110,138,138,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push164_1 : PushBound ⟨124,110,138,138,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push164_1]; exact allowed)
  have checked := c1493 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume0_0 (pattern : Ten) : pushGuard ⟨128,142,114,114,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume0_0 : ConsumeBound ⟨128,142,114,114,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume0_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume0_1 (pattern : Ten) : pushGuard ⟨128,142,114,114,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume0_1 : ConsumeBound ⟨128,142,114,114,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume0_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume1_0 (pattern : Ten) : pushGuard ⟨128,114,142,142,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume1_0 : ConsumeBound ⟨128,114,142,142,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume1_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume1_1 (pattern : Ten) : pushGuard ⟨128,114,142,142,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume1_1 : ConsumeBound ⟨128,114,142,142,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume1_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume18_0 (pattern : Ten) : pushGuard ⟨142,156,128,142,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume18_0 : ConsumeBound ⟨142,156,128,142,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume18_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume18_1 (pattern : Ten) : pushGuard ⟨142,156,128,142,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume18_1 : ConsumeBound ⟨142,156,128,142,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume18_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume20_0 (pattern : Ten) : pushGuard ⟨142,156,128,114,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume20_0 : ConsumeBound ⟨142,156,128,114,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume20_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume20_1 (pattern : Ten) : pushGuard ⟨142,156,128,114,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume20_1 : ConsumeBound ⟨142,156,128,114,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume20_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume21_0 (pattern : Ten) : pushGuard ⟨142,156,128,100,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume21_0 : ConsumeBound ⟨142,156,128,100,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume21_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume21_1 (pattern : Ten) : pushGuard ⟨142,156,128,100,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume21_1 : ConsumeBound ⟨142,156,128,100,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume21_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume22_0 (pattern : Ten) : pushGuard ⟨142,156,128,86,.north,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume22_0 : ConsumeBound ⟨142,156,128,86,.north,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume22_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume22_1 (pattern : Ten) : pushGuard ⟨142,156,128,86,.north,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume22_1 : ConsumeBound ⟨142,156,128,86,.north,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume22_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
end NetHack.Sokoban41
