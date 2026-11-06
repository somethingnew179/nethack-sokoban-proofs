/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers14
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_consume28_0 (pattern : Ten) : pushGuard ⟨143,142,144,144,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume28_0 : ConsumeBound ⟨143,142,144,144,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume28_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume28_1 (pattern : Ten) : pushGuard ⟨143,142,144,144,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume28_1 : ConsumeBound ⟨143,142,144,144,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume28_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume29_0 (pattern : Ten) : pushGuard ⟨143,144,142,142,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume29_0 : ConsumeBound ⟨143,144,142,142,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume29_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume29_1 (pattern : Ten) : pushGuard ⟨143,144,142,142,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume29_1 : ConsumeBound ⟨143,144,142,142,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume29_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume30_0 (pattern : Ten) : pushGuard ⟨144,143,145,145,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume30_0 : ConsumeBound ⟨144,143,145,145,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume30_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume30_1 (pattern : Ten) : pushGuard ⟨144,143,145,145,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume30_1 : ConsumeBound ⟨144,143,145,145,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume30_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume31_0 (pattern : Ten) : pushGuard ⟨144,145,143,143,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume31_0 : ConsumeBound ⟨144,145,143,143,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume31_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume31_1 (pattern : Ten) : pushGuard ⟨144,145,143,143,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume31_1 : ConsumeBound ⟨144,145,143,143,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume31_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume32_0 (pattern : Ten) : pushGuard ⟨145,144,146,146,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume32_0 : ConsumeBound ⟨145,144,146,146,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume32_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume32_1 (pattern : Ten) : pushGuard ⟨145,144,146,146,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume32_1 : ConsumeBound ⟨145,144,146,146,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume32_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume33_0 (pattern : Ten) : pushGuard ⟨145,146,144,144,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume33_0 : ConsumeBound ⟨145,146,144,144,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume33_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume33_1 (pattern : Ten) : pushGuard ⟨145,146,144,144,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume33_1 : ConsumeBound ⟨145,146,144,144,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume33_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume34_0 (pattern : Ten) : pushGuard ⟨146,145,147,146,.east,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume34_0 : ConsumeBound ⟨146,145,147,146,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume34_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume34_1 (pattern : Ten) : pushGuard ⟨146,145,147,146,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume34_1 : ConsumeBound ⟨146,145,147,146,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume34_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume41_0 (pattern : Ten) : pushGuard ⟨146,147,145,145,.west,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume41_0 : ConsumeBound ⟨146,147,145,145,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume41_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume41_1 (pattern : Ten) : pushGuard ⟨146,147,145,145,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume41_1 : ConsumeBound ⟨146,147,145,145,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume41_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume45_0 (pattern : Ten) : pushGuard ⟨147,148,146,146,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume45_0 : ConsumeBound ⟨147,148,146,146,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume45_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume45_1 (pattern : Ten) : pushGuard ⟨147,148,146,146,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume45_1 : ConsumeBound ⟨147,148,146,146,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume45_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume49_0 (pattern : Ten) : pushGuard ⟨148,149,147,146,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume49_0 : ConsumeBound ⟨148,149,147,146,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume49_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume49_1 (pattern : Ten) : pushGuard ⟨148,149,147,146,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume49_1 : ConsumeBound ⟨148,149,147,146,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume49_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume50_0 (pattern : Ten) : pushGuard ⟨148,149,147,145,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume50_0 : ConsumeBound ⟨148,149,147,145,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume50_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume50_1 (pattern : Ten) : pushGuard ⟨148,149,147,145,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume50_1 : ConsumeBound ⟨148,149,147,145,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume50_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume51_0 (pattern : Ten) : pushGuard ⟨148,149,147,144,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume51_0 : ConsumeBound ⟨148,149,147,144,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume51_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume51_1 (pattern : Ten) : pushGuard ⟨148,149,147,144,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume51_1 : ConsumeBound ⟨148,149,147,144,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume51_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume52_0 (pattern : Ten) : pushGuard ⟨148,149,147,143,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume52_0 : ConsumeBound ⟨148,149,147,143,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume52_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume52_1 (pattern : Ten) : pushGuard ⟨148,149,147,143,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume52_1 : ConsumeBound ⟨148,149,147,143,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume52_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume53_0 (pattern : Ten) : pushGuard ⟨148,149,147,142,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume53_0 : ConsumeBound ⟨148,149,147,142,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume53_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume53_1 (pattern : Ten) : pushGuard ⟨148,149,147,142,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume53_1 : ConsumeBound ⟨148,149,147,142,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume53_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume108_0 (pattern : Ten) : pushGuard ⟨87,86,88,88,.east,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume108_0 : ConsumeBound ⟨87,86,88,88,.east,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume108_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume108_1 (pattern : Ten) : pushGuard ⟨87,86,88,88,.east,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume108_1 : ConsumeBound ⟨87,86,88,88,.east,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume108_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume109_0 (pattern : Ten) : pushGuard ⟨87,88,86,86,.west,2,2,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume109_0 : ConsumeBound ⟨87,88,86,86,.west,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume109_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume109_1 (pattern : Ten) : pushGuard ⟨87,88,86,86,.west,2,2,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume109_1 : ConsumeBound ⟨87,88,86,86,.west,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume109_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume113_0 (pattern : Ten) : pushGuard ⟨89,90,88,88,.west,0,0,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume113_0 : ConsumeBound ⟨89,90,88,88,.west,0,0,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume113_0]; exact allowed)
  have checked := c1317 pattern guarded
  change d170 pattern ≤ (0 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume113_1 (pattern : Ten) : pushGuard ⟨89,90,88,88,.west,0,0,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume113_1 : ConsumeBound ⟨89,90,88,88,.west,0,0,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume113_1]; exact allowed)
  have checked := c1318 pattern guarded
  change d349 pattern ≤ (0 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume124_0 (pattern : Ten) : pushGuard ⟨100,114,86,86,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume124_0 : ConsumeBound ⟨100,114,86,86,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume124_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume124_1 (pattern : Ten) : pushGuard ⟨100,114,86,86,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume124_1 : ConsumeBound ⟨100,114,86,86,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume124_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume125_0 (pattern : Ten) : pushGuard ⟨100,86,114,114,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume125_0 : ConsumeBound ⟨100,86,114,114,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume125_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume125_1 (pattern : Ten) : pushGuard ⟨100,86,114,114,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume125_1 : ConsumeBound ⟨100,86,114,114,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume125_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume142_0 (pattern : Ten) : pushGuard ⟨114,128,100,100,.north,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume142_0 : ConsumeBound ⟨114,128,100,100,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume142_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume142_1 (pattern : Ten) : pushGuard ⟨114,128,100,100,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume142_1 : ConsumeBound ⟨114,128,100,100,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume142_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume143_0 (pattern : Ten) : pushGuard ⟨114,100,128,114,.south,1,1,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume143_0 : ConsumeBound ⟨114,100,128,114,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume143_0]; exact allowed)
  have checked := c1338 pattern guarded
  change d170 pattern ≤ (1 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume143_1 (pattern : Ten) : pushGuard ⟨114,100,128,114,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume143_1 : ConsumeBound ⟨114,100,128,114,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume143_1]; exact allowed)
  have checked := c1339 pattern guarded
  change d349 pattern ≤ (1 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
theorem guard_consume145_0 (pattern : Ten) : pushGuard ⟨114,100,128,142,.south,2,2,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume145_0 : ConsumeBound ⟨114,100,128,142,.south,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_consume145_0]; exact allowed)
  have checked := c1340 pattern guarded
  change d170 pattern ≤ (2 : Int) + d170 (change pattern 10 10)
  rw [s45]
  exact checked
theorem guard_consume145_1 (pattern : Ten) : pushGuard ⟨114,100,128,142,.south,2,2,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem consume145_1 : ConsumeBound ⟨114,100,128,142,.south,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_consume145_1]; exact allowed)
  have checked := c1341 pattern guarded
  change d349 pattern ≤ (2 : Int) + d349 (change pattern 10 10)
  rw [s99]
  exact checked
end NetHack.Sokoban41
