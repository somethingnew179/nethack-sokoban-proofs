/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Wrappers61
import NetHack.Sokoban21.Rows
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21
open Diagram
theorem guard_push133_0 (pattern : Twelve) : pushGuard ⟨109,110,108,108,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push133_0 : PushBound ⟨109,110,108,108,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push133_1 (pattern : Twelve) : pushGuard ⟨109,110,108,108,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push133_1 : PushBound ⟨109,110,108,108,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push133_2 (pattern : Twelve) : pushGuard ⟨109,110,108,108,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push133_2 : PushBound ⟨109,110,108,108,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push133_3 (pattern : Twelve) : pushGuard ⟨109,110,108,108,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push133_3 : PushBound ⟨109,110,108,108,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push133_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push134_0 (pattern : Twelve) : pushGuard ⟨110,130,90,90,.north,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push134_0 : PushBound ⟨110,130,90,90,.north,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push134_1 (pattern : Twelve) : pushGuard ⟨110,130,90,90,.north,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push134_1 : PushBound ⟨110,130,90,90,.north,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push134_2 (pattern : Twelve) : pushGuard ⟨110,130,90,90,.north,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push134_2 : PushBound ⟨110,130,90,90,.north,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push134_3 (pattern : Twelve) : pushGuard ⟨110,130,90,90,.north,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push134_3 : PushBound ⟨110,130,90,90,.north,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push134_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push135_0 (pattern : Twelve) : pushGuard ⟨110,109,111,111,.east,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push135_0 : PushBound ⟨110,109,111,111,.east,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push135_1 (pattern : Twelve) : pushGuard ⟨110,109,111,111,.east,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push135_1 : PushBound ⟨110,109,111,111,.east,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push135_2 (pattern : Twelve) : pushGuard ⟨110,109,111,111,.east,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push135_2 : PushBound ⟨110,109,111,111,.east,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push135_3 (pattern : Twelve) : pushGuard ⟨110,109,111,111,.east,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push135_3 : PushBound ⟨110,109,111,111,.east,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push135_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push136_0 (pattern : Twelve) : pushGuard ⟨110,90,130,130,.south,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push136_0 : PushBound ⟨110,90,130,130,.south,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push136_1 (pattern : Twelve) : pushGuard ⟨110,90,130,130,.south,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push136_1 : PushBound ⟨110,90,130,130,.south,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push136_2 (pattern : Twelve) : pushGuard ⟨110,90,130,130,.south,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push136_2 : PushBound ⟨110,90,130,130,.south,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push136_3 (pattern : Twelve) : pushGuard ⟨110,90,130,130,.south,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push136_3 : PushBound ⟨110,90,130,130,.south,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push136_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push137_0 (pattern : Twelve) : pushGuard ⟨110,111,109,109,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push137_0 : PushBound ⟨110,111,109,109,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push137_1 (pattern : Twelve) : pushGuard ⟨110,111,109,109,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push137_1 : PushBound ⟨110,111,109,109,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push137_2 (pattern : Twelve) : pushGuard ⟨110,111,109,109,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push137_2 : PushBound ⟨110,111,109,109,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push137_3 (pattern : Twelve) : pushGuard ⟨110,111,109,109,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push137_3 : PushBound ⟨110,111,109,109,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push137_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push138_0 (pattern : Twelve) : pushGuard ⟨111,110,112,112,.east,1,1,false,true⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push138_0 : PushBound ⟨111,110,112,112,.east,1,1,false,true⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_0]; exact allowed)
  have checked := c18628 pattern guarded
  change d156 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push138_1 (pattern : Twelve) : pushGuard ⟨111,110,112,112,.east,1,1,false,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push138_1 : PushBound ⟨111,110,112,112,.east,1,1,false,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_1]; exact allowed)
  have checked := c18699 pattern guarded
  change d907 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push138_2 (pattern : Twelve) : pushGuard ⟨111,110,112,112,.east,1,1,false,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push138_2 : PushBound ⟨111,110,112,112,.east,1,1,false,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_2]; exact allowed)
  have checked := c18763 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem guard_push138_3 (pattern : Twelve) : pushGuard ⟨111,110,112,112,.east,1,1,false,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push138_3 : PushBound ⟨111,110,112,112,.east,1,1,false,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push138_3]; exact allowed)
  have checked := c18800 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d6 (change pattern 12 12)
  rw [s20]
  exact checked
theorem guard_push139_0 (pattern : Twelve) : pushGuard ⟨111,112,110,110,.west,1,1,false,false⟩ 0 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push139_0 : PushBound ⟨111,112,110,110,.west,1,1,false,false⟩ 0 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_0]; exact allowed)
  have checked := c18536 pattern guarded
  change d156 pattern ≤ (1 : Int) + d156 (change pattern 12 12)
  rw [s4884]
  exact checked
theorem guard_push139_1 (pattern : Twelve) : pushGuard ⟨111,112,110,110,.west,1,1,false,false⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push139_1 : PushBound ⟨111,112,110,110,.west,1,1,false,false⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_1]; exact allowed)
  have checked := c9811 pattern guarded
  change d907 pattern ≤ (1 : Int) + d907 (change pattern 12 12)
  rw [s213]
  exact checked
theorem guard_push139_2 (pattern : Twelve) : pushGuard ⟨111,112,110,110,.west,1,1,false,false⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push139_2 : PushBound ⟨111,112,110,110,.west,1,1,false,false⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_2]; exact allowed)
  have checked := c9812 pattern guarded
  change d1354 pattern ≤ (1 : Int) + d1354 (change pattern 12 12)
  rw [s243]
  exact checked
theorem guard_push139_3 (pattern : Twelve) : pushGuard ⟨111,112,110,110,.west,1,1,false,false⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push139_3 : PushBound ⟨111,112,110,110,.west,1,1,false,false⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push139_3]; exact allowed)
  have checked := c9813 pattern guarded
  change d1678 pattern ≤ (1 : Int) + d1678 (change pattern 12 12)
  rw [s260]
  exact checked
theorem push140_0 : PushBound ⟨114,134,94,94,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push140_1 (pattern : Twelve) : pushGuard ⟨114,134,94,94,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push140_1 : PushBound ⟨114,134,94,94,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push140_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push140_2 (pattern : Twelve) : pushGuard ⟨114,134,94,94,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push140_2 : PushBound ⟨114,134,94,94,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push140_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push140_3 (pattern : Twelve) : pushGuard ⟨114,134,94,94,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push140_3 : PushBound ⟨114,134,94,94,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push140_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push141_0 : PushBound ⟨114,94,134,134,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push141_1 (pattern : Twelve) : pushGuard ⟨114,94,134,134,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push141_1 : PushBound ⟨114,94,134,134,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push141_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push141_2 (pattern : Twelve) : pushGuard ⟨114,94,134,134,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push141_2 : PushBound ⟨114,94,134,134,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push141_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push141_3 (pattern : Twelve) : pushGuard ⟨114,94,134,134,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push141_3 : PushBound ⟨114,94,134,134,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push141_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push142_0 : PushBound ⟨115,135,95,95,.north,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push142_1 (pattern : Twelve) : pushGuard ⟨115,135,95,95,.north,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push142_1 : PushBound ⟨115,135,95,95,.north,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push142_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push142_2 (pattern : Twelve) : pushGuard ⟨115,135,95,95,.north,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push142_2 : PushBound ⟨115,135,95,95,.north,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push142_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push142_3 (pattern : Twelve) : pushGuard ⟨115,135,95,95,.north,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push142_3 : PushBound ⟨115,135,95,95,.north,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push142_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push143_0 : PushBound ⟨115,114,116,116,.east,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push143_1 (pattern : Twelve) : pushGuard ⟨115,114,116,116,.east,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push143_1 : PushBound ⟨115,114,116,116,.east,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push143_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push143_2 (pattern : Twelve) : pushGuard ⟨115,114,116,116,.east,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push143_2 : PushBound ⟨115,114,116,116,.east,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push143_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push143_3 (pattern : Twelve) : pushGuard ⟨115,114,116,116,.east,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push143_3 : PushBound ⟨115,114,116,116,.east,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push143_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push144_0 : PushBound ⟨115,95,135,135,.south,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push144_1 (pattern : Twelve) : pushGuard ⟨115,95,135,135,.south,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push144_1 : PushBound ⟨115,95,135,135,.south,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push144_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
theorem guard_push144_2 (pattern : Twelve) : pushGuard ⟨115,95,135,135,.south,1,1,true,true⟩ 2 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push144_2 : PushBound ⟨115,95,135,135,.south,1,1,true,true⟩ 2 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push144_2]; exact allowed)
  have checked := c9815 pattern guarded
  change d1367 pattern ≤ (1 : Int) + d1367 (change pattern 12 12)
  rw [s326]
  exact checked
theorem guard_push144_3 (pattern : Twelve) : pushGuard ⟨115,95,135,135,.south,1,1,true,true⟩ 3 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push144_3 : PushBound ⟨115,95,135,135,.south,1,1,true,true⟩ 3 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push144_3]; exact allowed)
  have checked := c9816 pattern guarded
  change d1685 pattern ≤ (1 : Int) + d1685 (change pattern 12 12)
  rw [s333]
  exact checked
theorem push145_0 : PushBound ⟨115,116,114,114,.west,1,1,true,true⟩ 0 := by
  intro pattern allowed
  simp [pushGuard, budgetGuard] at allowed
theorem guard_push145_1 (pattern : Twelve) : pushGuard ⟨115,116,114,114,.west,1,1,true,true⟩ 1 pattern = decide (d1 pattern = 1) := by
  cases pattern with
  | mk a b c d e f g h i j k l =>
    rfl
theorem push145_1 : PushBound ⟨115,116,114,114,.west,1,1,true,true⟩ 1 := by
  intro pattern allowed
  have guarded : d1 pattern = 1 := of_decide_eq_true (by rw [← guard_push145_1]; exact allowed)
  have checked := c9814 pattern guarded
  change d926 pattern ≤ (1 : Int) + d926 (change pattern 12 12)
  rw [s313]
  exact checked
end NetHack.Sokoban21
