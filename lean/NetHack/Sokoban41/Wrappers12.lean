/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.Wrappers11
import NetHack.Sokoban41.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41
open Diagram
theorem guard_push66_0 (pattern : Ten) : pushGuard ⟨32,46,18,18,.north,2,2,false,true⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push66_0 : PushBound ⟨32,46,18,18,.north,2,2,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_0]; exact allowed)
  have checked := c2001 pattern guarded
  change d37 pattern ≤ (2 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push66_1 (pattern : Ten) : pushGuard ⟨32,46,18,18,.north,2,2,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push66_1 : PushBound ⟨32,46,18,18,.north,2,2,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push66_1]; exact allowed)
  have checked := c2027 pattern guarded
  change d192 pattern ≤ (2 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push67_0 (pattern : Ten) : pushGuard ⟨32,18,46,46,.south,0,2,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push67_0 : PushBound ⟨32,18,46,46,.south,0,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push67_1 (pattern : Ten) : pushGuard ⟨32,18,46,46,.south,0,2,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push67_1 : PushBound ⟨32,18,46,46,.south,0,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push67_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ (0 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push68_0 (pattern : Ten) : pushGuard ⟨37,51,23,23,.north,7,7,false,true⟩ 0 pattern = decide (d362 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem push68_0 : PushBound ⟨37,51,23,23,.north,7,7,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d362 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_0]; exact allowed)
  have checked := c2078 pattern guarded
  change d133 pattern ≤ (7 : Int) + d220 (change pattern 10 10)
  rw [s130]
  exact checked
theorem guard_push68_1 (pattern : Ten) : pushGuard ⟨37,51,23,23,.north,7,7,false,true⟩ 1 pattern = decide (d361 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem push68_1 : PushBound ⟨37,51,23,23,.north,7,7,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d361 pattern = 1 := of_decide_eq_true (by rw [← guard_push68_1]; exact allowed)
  have checked := c2109 pattern guarded
  change d289 pattern ≤ (7 : Int) + d10 (change pattern 10 10)
  rw [s4]
  exact checked
theorem guard_push69_0 (pattern : Ten) : pushGuard ⟨37,23,51,51,.south,0,7,false,false⟩ 0 pattern = decide (d362 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem push69_0 : PushBound ⟨37,23,51,51,.south,0,7,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d362 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_0]; exact allowed)
  have checked := c2149 pattern guarded
  change d66 pattern ≤ (0 : Int) + d66 (change pattern 10 3)
  rw [s316]
  exact checked
theorem guard_push69_1 (pattern : Ten) : pushGuard ⟨37,23,51,51,.south,0,7,false,false⟩ 1 pattern = decide (d361 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> rfl
theorem push69_1 : PushBound ⟨37,23,51,51,.south,0,7,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d361 pattern = 1 := of_decide_eq_true (by rw [← guard_push69_1]; exact allowed)
  have checked := c2187 pattern guarded
  change d220 pattern ≤ (0 : Int) + d220 (change pattern 10 3)
  rw [s331]
  exact checked
theorem guard_push70_0 (pattern : Ten) : pushGuard ⟨38,52,24,24,.north,8,8,false,true⟩ 0 pattern = decide (d433 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem push70_0 : PushBound ⟨38,52,24,24,.north,8,8,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d433 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_0]; exact allowed)
  have checked := c2233 pattern guarded
  change d135 pattern ≤ (8 : Int) + d238 (change pattern 2 10)
  rw [s362]
  exact checked
theorem guard_push70_1 (pattern : Ten) : pushGuard ⟨38,52,24,24,.north,8,8,false,true⟩ 1 pattern = decide (d436 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem push70_1 : PushBound ⟨38,52,24,24,.north,8,8,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d436 pattern = 1 := of_decide_eq_true (by rw [← guard_push70_1]; exact allowed)
  have checked := c2266 pattern guarded
  change d291 pattern ≤ (8 : Int) + d10 (change pattern 2 10)
  rw [s342]
  exact checked
theorem guard_push71_0 (pattern : Ten) : pushGuard ⟨38,37,39,39,.east,8,8,false,true⟩ 0 pattern = decide (d432 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem push71_0 : PushBound ⟨38,37,39,39,.east,8,8,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d432 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_0]; exact allowed)
  have checked := c2317 pattern guarded
  change d66 pattern ≤ (8 : Int) + d238 (change pattern 2 10)
  rw [s362]
  exact checked
theorem guard_push71_1 (pattern : Ten) : pushGuard ⟨38,37,39,39,.east,8,8,false,true⟩ 1 pattern = decide (d355 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem push71_1 : PushBound ⟨38,37,39,39,.east,8,8,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d355 pattern = 1 := of_decide_eq_true (by rw [← guard_push71_1]; exact allowed)
  have checked := c2334 pattern guarded
  change d220 pattern ≤ (8 : Int) + d10 (change pattern 2 10)
  rw [s342]
  exact checked
theorem guard_push72_0 (pattern : Ten) : pushGuard ⟨38,24,52,52,.south,0,8,false,false⟩ 0 pattern = decide (d433 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem push72_0 : PushBound ⟨38,24,52,52,.south,0,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d433 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_0]; exact allowed)
  have checked := c2357 pattern guarded
  change d66 pattern ≤ (0 : Int) + d85 (change pattern 2 4)
  rw [s390]
  exact checked
theorem guard_push72_1 (pattern : Ten) : pushGuard ⟨38,24,52,52,.south,0,8,false,false⟩ 1 pattern = decide (d436 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> rfl
theorem push72_1 : PushBound ⟨38,24,52,52,.south,0,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d436 pattern = 1 := of_decide_eq_true (by rw [← guard_push72_1]; exact allowed)
  have checked := c2375 pattern guarded
  change d220 pattern ≤ (0 : Int) + d238 (change pattern 2 4)
  rw [s412]
  exact checked
theorem guard_push73_0 (pattern : Ten) : pushGuard ⟨38,39,37,37,.west,2,8,false,false⟩ 0 pattern = decide (d432 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem push73_0 : PushBound ⟨38,39,37,37,.west,2,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d432 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_0]; exact allowed)
  have checked := c2406 pattern guarded
  change d66 pattern ≤ (2 : Int) + d85 (change pattern 2 10)
  rw [s433]
  exact checked
theorem guard_push73_1 (pattern : Ten) : pushGuard ⟨38,39,37,37,.west,2,8,false,false⟩ 1 pattern = decide (d355 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases f <;> rfl
theorem push73_1 : PushBound ⟨38,39,37,37,.west,2,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d355 pattern = 1 := of_decide_eq_true (by rw [← guard_push73_1]; exact allowed)
  have checked := c2449 pattern guarded
  change d220 pattern ≤ (2 : Int) + d238 (change pattern 2 10)
  rw [s362]
  exact checked
theorem push74_0 : PushBound ⟨39,53,25,25,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push74_1 (pattern : Ten) : pushGuard ⟨39,53,25,25,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push74_1 : PushBound ⟨39,53,25,25,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push74_1]; exact allowed)
  have checked := c2474 pattern guarded
  change d300 pattern ≤ (1 : Int) + d220 (change pattern 10 10)
  rw [s130]
  exact checked
theorem push75_0 : PushBound ⟨39,25,53,53,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push75_1 (pattern : Ten) : pushGuard ⟨39,25,53,53,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push75_1 : PushBound ⟨39,25,53,53,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push75_1]; exact allowed)
  have checked := c2486 pattern guarded
  change d220 pattern ≤ (1 : Int) + d220 (change pattern 10 5)
  rw [s476]
  exact checked
theorem push76_0 : PushBound ⟨43,57,29,29,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push76_1 (pattern : Ten) : pushGuard ⟨43,57,29,29,.north,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push76_1 : PushBound ⟨43,57,29,29,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push76_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem push77_0 : PushBound ⟨43,29,57,57,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push77_1 (pattern : Ten) : pushGuard ⟨43,29,57,57,.south,1,1,true,true⟩ 1 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push77_1 : PushBound ⟨43,29,57,57,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push77_1]; exact allowed)
  have checked := c1645 pattern guarded
  change d192 pattern ≤ (1 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push78_0 (pattern : Ten) : pushGuard ⟨44,58,30,30,.north,1,1,false,false⟩ 0 pattern = decide (d447 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push78_0 : PushBound ⟨44,58,30,30,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d447 pattern = 1 := of_decide_eq_true (by rw [← guard_push78_0]; exact allowed)
  have checked := c2510 pattern guarded
  change d37 pattern ≤ (1 : Int) + d37 (change pattern 1 0)
  rw [s506]
  exact checked
theorem guard_push78_1 (pattern : Ten) : pushGuard ⟨44,58,30,30,.north,1,1,false,false⟩ 1 pattern = decide (d446 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push78_1 : PushBound ⟨44,58,30,30,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d446 pattern = 1 := of_decide_eq_true (by rw [← guard_push78_1]; exact allowed)
  have checked := c2535 pattern guarded
  change d192 pattern ≤ (1 : Int) + d248 (change pattern 1 0)
  rw [s533]
  exact checked
theorem guard_push79_0 (pattern : Ten) : pushGuard ⟨44,43,45,45,.east,0,1,false,false⟩ 0 pattern = decide (d445 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push79_0 : PushBound ⟨44,43,45,45,.east,0,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d445 pattern = 1 := of_decide_eq_true (by rw [← guard_push79_0]; exact allowed)
  have checked := c2536 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 1 10)
  rw [s564]
  exact checked
theorem guard_push79_1 (pattern : Ten) : pushGuard ⟨44,43,45,45,.east,0,1,false,false⟩ 1 pattern = decide (d360 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push79_1 : PushBound ⟨44,43,45,45,.east,0,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d360 pattern = 1 := of_decide_eq_true (by rw [← guard_push79_1]; exact allowed)
  have checked := c2537 pattern guarded
  change d192 pattern ≤ (0 : Int) + d248 (change pattern 1 10)
  rw [s592]
  exact checked
theorem guard_push80_0 (pattern : Ten) : pushGuard ⟨44,30,58,58,.south,1,1,false,true⟩ 0 pattern = decide (d447 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push80_0 : PushBound ⟨44,30,58,58,.south,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d447 pattern = 1 := of_decide_eq_true (by rw [← guard_push80_0]; exact allowed)
  have checked := c2572 pattern guarded
  change d81 pattern ≤ (1 : Int) + d248 (change pattern 1 10)
  rw [s592]
  exact checked
theorem guard_push80_1 (pattern : Ten) : pushGuard ⟨44,30,58,58,.south,1,1,false,true⟩ 1 pattern = decide (d446 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases f <;> rfl
theorem push80_1 : PushBound ⟨44,30,58,58,.south,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d446 pattern = 1 := of_decide_eq_true (by rw [← guard_push80_1]; exact allowed)
  have checked := c2598 pattern guarded
  change d234 pattern ≤ (1 : Int) + d10 (change pattern 1 10)
  rw [s535]
  exact checked
theorem guard_push81_0 (pattern : Ten) : pushGuard ⟨44,45,43,43,.west,1,1,false,true⟩ 0 pattern = decide (d445 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push81_0 : PushBound ⟨44,45,43,43,.west,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d445 pattern = 1 := of_decide_eq_true (by rw [← guard_push81_0]; exact allowed)
  have checked := c2632 pattern guarded
  change d37 pattern ≤ (1 : Int) + d248 (change pattern 1 10)
  rw [s592]
  exact checked
theorem guard_push81_1 (pattern : Ten) : pushGuard ⟨44,45,43,43,.west,1,1,false,true⟩ 1 pattern = decide (d360 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push81_1 : PushBound ⟨44,45,43,43,.west,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d360 pattern = 1 := of_decide_eq_true (by rw [← guard_push81_1]; exact allowed)
  have checked := c2657 pattern guarded
  change d192 pattern ≤ (1 : Int) + d10 (change pattern 1 10)
  rw [s535]
  exact checked
theorem guard_push82_0 (pattern : Ten) : pushGuard ⟨45,44,46,46,.east,0,2,false,false⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push82_0 : PushBound ⟨45,44,46,46,.east,0,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_push82_0]; exact allowed)
  have checked := c89 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push82_1 (pattern : Ten) : pushGuard ⟨45,44,46,46,.east,0,2,false,false⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push82_1 : PushBound ⟨45,44,46,46,.east,0,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_push82_1]; exact allowed)
  have checked := c391 pattern guarded
  change d248 pattern ≤ (0 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push83_0 (pattern : Ten) : pushGuard ⟨45,46,44,44,.west,2,2,false,false⟩ 0 pattern = decide (d357 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push83_0 : PushBound ⟨45,46,44,44,.west,2,2,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d357 pattern = 1 := of_decide_eq_true (by rw [← guard_push83_0]; exact allowed)
  have checked := c2658 pattern guarded
  change d37 pattern ≤ (2 : Int) + d37 (change pattern 10 1)
  rw [s623]
  exact checked
theorem guard_push83_1 (pattern : Ten) : pushGuard ⟨45,46,44,44,.west,2,2,false,false⟩ 1 pattern = decide (d356 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases b <;> cases f <;> rfl
theorem push83_1 : PushBound ⟨45,46,44,44,.west,2,2,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d356 pattern = 1 := of_decide_eq_true (by rw [← guard_push83_1]; exact allowed)
  have checked := c2659 pattern guarded
  change d192 pattern ≤ (2 : Int) + d192 (change pattern 10 1)
  rw [s647]
  exact checked
theorem guard_push84_0 (pattern : Ten) : pushGuard ⟨46,45,47,47,.east,0,3,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push84_0 : PushBound ⟨46,45,47,47,.east,0,3,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push84_0]; exact allowed)
  have checked := c0 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push84_1 (pattern : Ten) : pushGuard ⟨46,45,47,47,.east,0,3,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push84_1 : PushBound ⟨46,45,47,47,.east,0,3,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push84_1]; exact allowed)
  have checked := c1 pattern guarded
  change d192 pattern ≤ (0 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push85_0 (pattern : Ten) : pushGuard ⟨46,47,45,45,.west,2,3,false,false⟩ 0 pattern = decide (d350 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push85_0 : PushBound ⟨46,47,45,45,.west,2,3,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d350 pattern = 1 := of_decide_eq_true (by rw [← guard_push85_0]; exact allowed)
  have checked := c2660 pattern guarded
  change d37 pattern ≤ (2 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push85_1 (pattern : Ten) : pushGuard ⟨46,47,45,45,.west,2,3,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push85_1 : PushBound ⟨46,47,45,45,.west,2,3,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push85_1]; exact allowed)
  have checked := c2661 pattern guarded
  change d192 pattern ≤ (2 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push86_0 (pattern : Ten) : pushGuard ⟨47,46,48,48,.east,0,4,false,false⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem push86_0 : PushBound ⟨47,46,48,48,.east,0,4,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_push86_0]; exact allowed)
  have checked := c2693 pattern guarded
  change d37 pattern ≤ (0 : Int) + d37 (change pattern 10 9)
  rw [s678]
  exact checked
theorem guard_push86_1 (pattern : Ten) : pushGuard ⟨47,46,48,48,.east,0,4,false,false⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem push86_1 : PushBound ⟨47,46,48,48,.east,0,4,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_push86_1]; exact allowed)
  have checked := c2718 pattern guarded
  change d192 pattern ≤ (0 : Int) + d192 (change pattern 10 9)
  rw [s702]
  exact checked
theorem guard_push87_0 (pattern : Ten) : pushGuard ⟨47,48,46,46,.west,2,4,false,false⟩ 0 pattern = decide (d384 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem push87_0 : PushBound ⟨47,48,46,46,.west,2,4,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d384 pattern = 1 := of_decide_eq_true (by rw [← guard_push87_0]; exact allowed)
  have checked := c2754 pattern guarded
  change d107 pattern ≤ (2 : Int) + d37 (change pattern 10 10)
  rw [s243]
  exact checked
theorem guard_push87_1 (pattern : Ten) : pushGuard ⟨47,48,46,46,.west,2,4,false,false⟩ 1 pattern = decide (d383 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases j <;> rfl
theorem push87_1 : PushBound ⟨47,48,46,46,.west,2,4,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d383 pattern = 1 := of_decide_eq_true (by rw [← guard_push87_1]; exact allowed)
  have checked := c2782 pattern guarded
  change d265 pattern ≤ (2 : Int) + d192 (change pattern 10 10)
  rw [s118]
  exact checked
theorem guard_push88_0 (pattern : Ten) : pushGuard ⟨48,47,49,49,.east,0,5,false,false⟩ 0 pattern = decide (d451 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push88_0 : PushBound ⟨48,47,49,49,.east,0,5,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d451 pattern = 1 := of_decide_eq_true (by rw [← guard_push88_0]; exact allowed)
  have checked := c2813 pattern guarded
  change d37 pattern ≤ (0 : Int) + d107 (change pattern 9 8)
  rw [s728]
  exact checked
theorem guard_push88_1 (pattern : Ten) : pushGuard ⟨48,47,49,49,.east,0,5,false,false⟩ 1 pattern = decide (d460 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push88_1 : PushBound ⟨48,47,49,49,.east,0,5,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d460 pattern = 1 := of_decide_eq_true (by rw [← guard_push88_1]; exact allowed)
  have checked := c2837 pattern guarded
  change d192 pattern ≤ (0 : Int) + d265 (change pattern 9 8)
  rw [s749]
  exact checked
theorem guard_push89_0 (pattern : Ten) : pushGuard ⟨48,49,47,47,.west,2,5,false,false⟩ 0 pattern = decide (d451 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push89_0 : PushBound ⟨48,49,47,47,.west,2,5,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d451 pattern = 1 := of_decide_eq_true (by rw [← guard_push89_0]; exact allowed)
  have checked := c2874 pattern guarded
  change d123 pattern ≤ (2 : Int) + d107 (change pattern 9 10)
  rw [s776]
  exact checked
theorem guard_push89_1 (pattern : Ten) : pushGuard ⟨48,49,47,47,.west,2,5,false,false⟩ 1 pattern = decide (d460 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases i <;> cases j <;> rfl
theorem push89_1 : PushBound ⟨48,49,47,47,.west,2,5,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d460 pattern = 1 := of_decide_eq_true (by rw [← guard_push89_1]; exact allowed)
  have checked := c2899 pattern guarded
  change d279 pattern ≤ (2 : Int) + d265 (change pattern 9 10)
  rw [s798]
  exact checked
theorem guard_push90_0 (pattern : Ten) : pushGuard ⟨49,48,50,50,.east,0,6,false,false⟩ 0 pattern = decide (d480 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> cases j <;> rfl
theorem push90_0 : PushBound ⟨49,48,50,50,.east,0,6,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d480 pattern = 1 := of_decide_eq_true (by rw [← guard_push90_0]; exact allowed)
  have checked := c2927 pattern guarded
  change d107 pattern ≤ (0 : Int) + d123 (change pattern 8 7)
  rw [s822]
  exact checked
theorem guard_push90_1 (pattern : Ten) : pushGuard ⟨49,48,50,50,.east,0,6,false,false⟩ 1 pattern = decide (d487 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> cases j <;> rfl
theorem push90_1 : PushBound ⟨49,48,50,50,.east,0,6,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d487 pattern = 1 := of_decide_eq_true (by rw [← guard_push90_1]; exact allowed)
  have checked := c2949 pattern guarded
  change d265 pattern ≤ (0 : Int) + d279 (change pattern 8 7)
  rw [s843]
  exact checked
theorem guard_push91_0 (pattern : Ten) : pushGuard ⟨49,50,48,48,.west,2,6,false,false⟩ 0 pattern = decide (d480 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> cases j <;> rfl
theorem push91_0 : PushBound ⟨49,50,48,48,.west,2,6,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d480 pattern = 1 := of_decide_eq_true (by rw [← guard_push91_0]; exact allowed)
  have checked := c2977 pattern guarded
  change d132 pattern ≤ (2 : Int) + d123 (change pattern 8 9)
  rw [s865]
  exact checked
theorem guard_push91_1 (pattern : Ten) : pushGuard ⟨49,50,48,48,.west,2,6,false,false⟩ 1 pattern = decide (d487 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> cases h <;> cases i <;> cases j <;> rfl
theorem push91_1 : PushBound ⟨49,50,48,48,.west,2,6,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d487 pattern = 1 := of_decide_eq_true (by rw [← guard_push91_1]; exact allowed)
  have checked := c3001 pattern guarded
  change d288 pattern ≤ (2 : Int) + d279 (change pattern 8 9)
  rw [s885]
  exact checked
theorem guard_push92_0 (pattern : Ten) : pushGuard ⟨50,49,51,51,.east,0,7,false,false⟩ 0 pattern = decide (d519 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> cases i <;> rfl
theorem push92_0 : PushBound ⟨50,49,51,51,.east,0,7,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d519 pattern = 1 := of_decide_eq_true (by rw [← guard_push92_0]; exact allowed)
  have checked := c3020 pattern guarded
  change d123 pattern ≤ (0 : Int) + d132 (change pattern 7 3)
  rw [s905]
  exact checked
theorem guard_push92_1 (pattern : Ten) : pushGuard ⟨50,49,51,51,.east,0,7,false,false⟩ 1 pattern = decide (d521 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> cases i <;> rfl
theorem push92_1 : PushBound ⟨50,49,51,51,.east,0,7,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d521 pattern = 1 := of_decide_eq_true (by rw [← guard_push92_1]; exact allowed)
  have checked := c3037 pattern guarded
  change d279 pattern ≤ (0 : Int) + d288 (change pattern 7 3)
  rw [s924]
  exact checked
theorem guard_push93_0 (pattern : Ten) : pushGuard ⟨50,51,49,49,.west,2,7,false,false⟩ 0 pattern = decide (d519 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> cases i <;> rfl
theorem push93_0 : PushBound ⟨50,51,49,49,.west,2,7,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d519 pattern = 1 := of_decide_eq_true (by rw [← guard_push93_0]; exact allowed)
  have checked := c3053 pattern guarded
  change d133 pattern ≤ (2 : Int) + d132 (change pattern 7 8)
  rw [s941]
  exact checked
theorem guard_push93_1 (pattern : Ten) : pushGuard ⟨50,51,49,49,.west,2,7,false,false⟩ 1 pattern = decide (d521 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases f <;> cases h <;> cases i <;> rfl
theorem push93_1 : PushBound ⟨50,51,49,49,.west,2,7,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d521 pattern = 1 := of_decide_eq_true (by rw [← guard_push93_1]; exact allowed)
  have checked := c3068 pattern guarded
  change d289 pattern ≤ (2 : Int) + d288 (change pattern 7 8)
  rw [s958]
  exact checked
theorem guard_push94_0 (pattern : Ten) : pushGuard ⟨51,50,52,52,.east,0,8,false,false⟩ 0 pattern = decide (d539 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases h <;> rfl
theorem push94_0 : PushBound ⟨51,50,52,52,.east,0,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d539 pattern = 1 := of_decide_eq_true (by rw [← guard_push94_0]; exact allowed)
  have checked := c3072 pattern guarded
  change d132 pattern ≤ (0 : Int) + d133 (change pattern 3 4)
  rw [s985]
  exact checked
theorem guard_push94_1 (pattern : Ten) : pushGuard ⟨51,50,52,52,.east,0,8,false,false⟩ 1 pattern = decide (d542 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases h <;> rfl
theorem push94_1 : PushBound ⟨51,50,52,52,.east,0,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d542 pattern = 1 := of_decide_eq_true (by rw [← guard_push94_1]; exact allowed)
  have checked := c3075 pattern guarded
  change d288 pattern ≤ (0 : Int) + d289 (change pattern 3 4)
  rw [s1010]
  exact checked
theorem guard_push95_0 (pattern : Ten) : pushGuard ⟨51,52,50,50,.west,2,8,false,false⟩ 0 pattern = decide (d539 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases h <;> rfl
theorem push95_0 : PushBound ⟨51,52,50,50,.west,2,8,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d539 pattern = 1 := of_decide_eq_true (by rw [← guard_push95_0]; exact allowed)
  have checked := c3088 pattern guarded
  change d135 pattern ≤ (2 : Int) + d133 (change pattern 3 7)
  rw [s1025]
  exact checked
theorem guard_push95_1 (pattern : Ten) : pushGuard ⟨51,52,50,50,.west,2,8,false,false⟩ 1 pattern = decide (d542 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> cases h <;> rfl
theorem push95_1 : PushBound ⟨51,52,50,50,.west,2,8,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d542 pattern = 1 := of_decide_eq_true (by rw [← guard_push95_1]; exact allowed)
  have checked := c3094 pattern guarded
  change d291 pattern ≤ (2 : Int) + d289 (change pattern 3 7)
  rw [s1040]
  exact checked
theorem guard_push96_0 (pattern : Ten) : pushGuard ⟨52,66,38,38,.north,2,9,false,false⟩ 0 pattern = decide (d555 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> cases g <;> rfl
theorem push96_0 : PushBound ⟨52,66,38,38,.north,2,9,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d555 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_0]; exact allowed)
  have checked := c3105 pattern guarded
  change d156 pattern ≤ (2 : Int) + d135 (change pattern 4 2)
  rw [s1060]
  exact checked
theorem guard_push96_1 (pattern : Ten) : pushGuard ⟨52,66,38,38,.north,2,9,false,false⟩ 1 pattern = decide (d559 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> cases g <;> rfl
theorem push96_1 : PushBound ⟨52,66,38,38,.north,2,9,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d559 pattern = 1 := of_decide_eq_true (by rw [← guard_push96_1]; exact allowed)
  have checked := c3140 pattern guarded
  change d331 pattern ≤ (2 : Int) + d291 (change pattern 4 2)
  rw [s1080]
  exact checked
theorem guard_push97_0 (pattern : Ten) : pushGuard ⟨52,51,53,53,.east,9,9,false,true⟩ 0 pattern = decide (d562 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem push97_0 : PushBound ⟨52,51,53,53,.east,9,9,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d562 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_0]; exact allowed)
  have checked := c3226 pattern guarded
  change d133 pattern ≤ (9 : Int) + d291 (change pattern 4 5)
  rw [s1107]
  exact checked
theorem guard_push97_1 (pattern : Ten) : pushGuard ⟨52,51,53,53,.east,9,9,false,true⟩ 1 pattern = decide (d562 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem push97_1 : PushBound ⟨52,51,53,53,.east,9,9,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d562 pattern = 1 := of_decide_eq_true (by rw [← guard_push97_1]; exact allowed)
  have checked := c3269 pattern guarded
  change d289 pattern ≤ (9 : Int) + d10 (change pattern 4 5)
  rw [s1091]
  exact checked
theorem guard_push98_0 (pattern : Ten) : pushGuard ⟨52,38,66,66,.south,0,9,false,false⟩ 0 pattern = decide (d555 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> cases g <;> rfl
theorem push98_0 : PushBound ⟨52,38,66,66,.south,0,9,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d555 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_0]; exact allowed)
  have checked := c3277 pattern guarded
  change d85 pattern ≤ (0 : Int) + d135 (change pattern 4 6)
  rw [s1127]
  exact checked
theorem guard_push98_1 (pattern : Ten) : pushGuard ⟨52,38,66,66,.south,0,9,false,false⟩ 1 pattern = decide (d559 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases c <;> cases e <;> cases f <;> cases g <;> rfl
theorem push98_1 : PushBound ⟨52,38,66,66,.south,0,9,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d559 pattern = 1 := of_decide_eq_true (by rw [← guard_push98_1]; exact allowed)
  have checked := c3285 pattern guarded
  change d238 pattern ≤ (0 : Int) + d291 (change pattern 4 6)
  rw [s1147]
  exact checked
theorem guard_push99_0 (pattern : Ten) : pushGuard ⟨52,53,51,51,.west,2,9,false,false⟩ 0 pattern = decide (d562 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem push99_0 : PushBound ⟨52,53,51,51,.west,2,9,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d562 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_0]; exact allowed)
  have checked := c3326 pattern guarded
  change d66 pattern ≤ (2 : Int) + d135 (change pattern 4 3)
  rw [s1156]
  exact checked
theorem guard_push99_1 (pattern : Ten) : pushGuard ⟨52,53,51,51,.west,2,9,false,false⟩ 1 pattern = decide (d562 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases d <;> cases e <;> cases f <;> rfl
theorem push99_1 : PushBound ⟨52,53,51,51,.west,2,9,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d562 pattern = 1 := of_decide_eq_true (by rw [← guard_push99_1]; exact allowed)
  have checked := c3372 pattern guarded
  change d300 pattern ≤ (2 : Int) + d291 (change pattern 4 3)
  rw [s1162]
  exact checked
theorem push100_0 : PushBound ⟨53,67,39,39,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push100_1 (pattern : Ten) : pushGuard ⟨53,67,39,39,.north,1,1,true,true⟩ 1 pattern = decide (d379 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases f <;> rfl
theorem push100_1 : PushBound ⟨53,67,39,39,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d379 pattern = 1 := of_decide_eq_true (by rw [← guard_push100_1]; exact allowed)
  have checked := c3419 pattern guarded
  change d340 pattern ≤ (1 : Int) + d300 (change pattern 5 10)
  rw [s1204]
  exact checked
end NetHack.Sokoban41
