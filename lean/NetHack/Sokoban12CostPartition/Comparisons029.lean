/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4060 (p : Pattern) (guard : d1053 p = 1) : d483 p ≤ (0 : Int) + d522 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d483, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d483, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d483, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d483, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4061 (p : Pattern) (guard : d1053 p = 1) : d484 p ≤ (0 : Int) + d523 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d484, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4055 p hg
    simpa only [d484, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d484, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4060 p hg
    simpa only [d484, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4062 (p : Pattern) (guard : d1053 p = 1) : d485 p ≤ (0 : Int) + d524 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d485, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4040 p hg
    simpa only [d485, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d485, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d485, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4063 (p : Pattern) (guard : d1054 p = 1) : d56 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d1054, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4064 (p : Pattern) (guard : d1054 p = 1) : d62 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d1054, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4065 (p : Pattern) (guard : d1054 p = 1) : d451 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4066 (p : Pattern) (guard : d1054 p = 1) : d452 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1054, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d1054, d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4067 (p : Pattern) (guard : d1054 p = 1) : d453 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1054, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d1054, d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4068 (p : Pattern) (guard : d1054 p = 1) : d454 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4066 p hg
    simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4067 p hg
    simpa only [d454, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4069 (p : Pattern) (guard : d1054 p = 1) : d455 p ≤ (0 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d455, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4065 p hg
    simpa only [d455, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d455, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d455, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4070 (p : Pattern) (guard : d1054 p = 1) : d456 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4071 (p : Pattern) (guard : d1054 p = 1) : d457 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4072 (p : Pattern) (guard : d1054 p = 1) : d458 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4071 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4073 (p : Pattern) (guard : d1054 p = 1) : d459 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4066 p hg
    simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d459, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4074 (p : Pattern) (guard : d1054 p = 1) : d460 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4067 p hg
    simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d460, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4075 (p : Pattern) (guard : d1054 p = 1) : d461 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4074 p hg
    simpa only [d461, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4076 (p : Pattern) (guard : d1054 p = 1) : d462 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d462, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4072 p hg
    simpa only [d462, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d462, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d462, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4077 (p : Pattern) (guard : d1054 p = 1) : d463 p ≤ (0 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d463, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d463, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d463, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d463, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4078 (p : Pattern) (guard : d1054 p = 1) : d464 p ≤ (0 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d464, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d464, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d464, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d464, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4079 (p : Pattern) (guard : d1054 p = 1) : d465 p ≤ (0 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d465, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4077 p hg
    simpa only [d465, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d465, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4078 p hg
    simpa only [d465, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4080 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (0 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3828 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4081 (p : Pattern) (guard : d1053 p = 1) : d137 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d1053, d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1053, d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4082 (p : Pattern) (guard : d1054 p = 1) : d466 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d466, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d1054, d466, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d466, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d1054, d466, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4083 (p : Pattern) (guard : d1054 p = 1) : d467 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4082 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4084 (p : Pattern) (guard : d1054 p = 1) : d468 p ≤ (0 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4083 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4085 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (0 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3831 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4086 (p : Pattern) (guard : d1053 p = 1) : d143 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d1053, d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d1053, d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4087 (p : Pattern) (guard : d1053 p = 1) : d144 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4086 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4088 (p : Pattern) (guard : d1054 p = 1) : d469 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1054, d469, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d1054, d469, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d1054, d469, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4087 p hg
    simpa only [d1054, d469, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4089 (p : Pattern) (guard : d1054 p = 1) : d470 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4088 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4090 (p : Pattern) (guard : d1054 p = 1) : d471 p ≤ (0 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4089 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4091 (p : Pattern) (guard : d1054 p = 1) : d472 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d472, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d472, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d472, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d472, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4092 (p : Pattern) (guard : d1054 p = 1) : d473 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d473, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4091 p hg
    simpa only [d473, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d473, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d473, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4093 (p : Pattern) (guard : d1054 p = 1) : d474 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d474, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4082 p hg
    simpa only [d474, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d474, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d474, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4094 (p : Pattern) (guard : d1054 p = 1) : d475 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d475, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4088 p hg
    simpa only [d475, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d475, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d475, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4095 (p : Pattern) (guard : d1054 p = 1) : d476 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d476, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4093 p hg
    simpa only [d476, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d476, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4094 p hg
    simpa only [d476, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4096 (p : Pattern) (guard : d1054 p = 1) : d477 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d477, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d477, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d477, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d477, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4097 (p : Pattern) (guard : d1054 p = 1) : d478 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d478, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4092 p hg
    simpa only [d478, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d478, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d478, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4098 (p : Pattern) (guard : d1054 p = 1) : d479 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d479, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4083 p hg
    simpa only [d479, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d479, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d479, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4099 (p : Pattern) (guard : d1054 p = 1) : d480 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d480, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4089 p hg
    simpa only [d480, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d480, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d480, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4100 (p : Pattern) (guard : d1054 p = 1) : d481 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d481, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4098 p hg
    simpa only [d481, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d481, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4099 p hg
    simpa only [d481, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4101 (p : Pattern) (guard : d1054 p = 1) : d482 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d482, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d482, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d482, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d482, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4102 (p : Pattern) (guard : d1054 p = 1) : d483 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d483, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4101 p hg
    simpa only [d483, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d483, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d483, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4103 (p : Pattern) (guard : d1054 p = 1) : d484 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d484, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d484, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d484, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d484, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4104 (p : Pattern) (guard : d1054 p = 1) : d485 p ≤ (0 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1054 p = 1 := by simpa only [d485, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4079 p hg
    simpa only [d485, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1054 p = 1 := by simpa only [d485, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d485, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4105 (p : Pattern) (guard : d1015 p = 1) : d56 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4106 (p : Pattern) (guard : d1015 p = 1) : d62 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4107 (p : Pattern) (guard : d1015 p = 1) : d451 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d451, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d451, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d451, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d451, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4108 (p : Pattern) (guard : d0 p = 1) : d452 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4109 (p : Pattern) (guard : d1015 p = 1) : d452 p ≤ (0 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4110 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4111 (p : Pattern) (guard : d1015 p = 1) : d453 p ≤ (0 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4112 (p : Pattern) (guard : d1015 p = 1) : d454 p ≤ (0 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d454, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d454, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d454, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d454, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4113 (p : Pattern) (guard : d1015 p = 1) : d455 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d455, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4107 p hg
    simpa only [d455, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d455, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d455, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4114 (p : Pattern) (guard : d1015 p = 1) : d456 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d456, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d456, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d456, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d456, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4115 (p : Pattern) (guard : d1015 p = 1) : d457 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d457, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d457, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d457, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d457, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4116 (p : Pattern) (guard : d1015 p = 1) : d458 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d458, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d458, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d458, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d458, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4117 (p : Pattern) (guard : d1015 p = 1) : d459 p ≤ (0 : Int) + d211 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d459, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d459, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d459, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d459, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4118 (p : Pattern) (guard : d1015 p = 1) : d460 p ≤ (0 : Int) + d212 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d460, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d460, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d460, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d460, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4119 (p : Pattern) (guard : d1015 p = 1) : d461 p ≤ (0 : Int) + d213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d461, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4117 p hg
    simpa only [d461, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d461, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4118 p hg
    simpa only [d461, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4120 (p : Pattern) (guard : d1015 p = 1) : d462 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d462, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4116 p hg
    simpa only [d462, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d462, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4119 p hg
    simpa only [d462, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4121 (p : Pattern) (guard : d1015 p = 1) : d463 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d463, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d463, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d463, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d463, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4122 (p : Pattern) (guard : d1015 p = 1) : d464 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d464, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d464, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d464, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d464, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4123 (p : Pattern) (guard : d1015 p = 1) : d465 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d465, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d465, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d465, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4122 p hg
    simpa only [d465, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4124 (p : Pattern) (guard : d0 p = 1) : d466 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4125 (p : Pattern) (guard : d1015 p = 1) : d467 p ≤ (0 : Int) + d114 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d467, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d1015, d467, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d467, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4124 p hg
    simpa only [d1015, d467, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4126 (p : Pattern) (guard : d1015 p = 1) : d468 p ≤ (0 : Int) + d114 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4125 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4127 (p : Pattern) (guard : d0 p = 1) : d469 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4128 (p : Pattern) (guard : d1015 p = 1) : d470 p ≤ (0 : Int) + d116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d470, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d1015, d470, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d470, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d1015, d470, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4129 (p : Pattern) (guard : d1015 p = 1) : d471 p ≤ (0 : Int) + d116 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4130 (p : Pattern) (guard : d1015 p = 1) : d472 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d472, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d472, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d472, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4129 p hg
    simpa only [d472, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4131 (p : Pattern) (guard : d1015 p = 1) : d473 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d473, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d473, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d473, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d473, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4132 (p : Pattern) (guard : d1015 p = 1) : d466 p ≤ (0 : Int) + d346 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3946 p hg
    simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4124 p hg
    simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4133 (p : Pattern) (guard : d1015 p = 1) : d474 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d474, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d474, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d474, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d474, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4134 (p : Pattern) (guard : d1015 p = 1) : d469 p ≤ (0 : Int) + d348 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3949 p hg
    simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4135 (p : Pattern) (guard : d1015 p = 1) : d475 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d475, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4134 p hg
    simpa only [d475, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d475, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d475, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4136 (p : Pattern) (guard : d1015 p = 1) : d476 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d476, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4133 p hg
    simpa only [d476, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d476, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4135 p hg
    simpa only [d476, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4137 (p : Pattern) (guard : d1015 p = 1) : d477 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d477, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4136 p hg
    simpa only [d477, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d477, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d477, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4138 (p : Pattern) (guard : d1015 p = 1) : d478 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d478, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4131 p hg
    simpa only [d478, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d478, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4137 p hg
    simpa only [d478, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4139 (p : Pattern) (guard : d1015 p = 1) : d479 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d479, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4125 p hg
    simpa only [d479, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d479, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d479, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4140 (p : Pattern) (guard : d1015 p = 1) : d480 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d480, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d480, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d480, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d480, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4141 (p : Pattern) (guard : d1015 p = 1) : d481 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d481, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4139 p hg
    simpa only [d481, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d481, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d481, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4142 (p : Pattern) (guard : d1015 p = 1) : d482 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d482, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4141 p hg
    simpa only [d482, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d482, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d482, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4143 (p : Pattern) (guard : d1015 p = 1) : d483 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d483, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4142 p hg
    simpa only [d483, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d483, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d483, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4144 (p : Pattern) (guard : d1015 p = 1) : d484 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d484, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4138 p hg
    simpa only [d484, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d484, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d484, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4145 (p : Pattern) (guard : d1015 p = 1) : d485 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d485, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d485, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d485, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4144 p hg
    simpa only [d485, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4146 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4147 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4146 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4148 (p : Pattern) (guard : d851 p = 1) : d502 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4149 (p : Pattern) (guard : d851 p = 1) : d143 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4150 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4146 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4149 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4151 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4150 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4152 (p : Pattern) (guard : d851 p = 1) : d504 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4153 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4154 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4155 (p : Pattern) (guard : d851 p = 1) : d507 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4156 (p : Pattern) (guard : d851 p = 1) : d508 p ≤ (0 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4155 p hg
    simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4157 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4158 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4159 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4157 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4158 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4160 (p : Pattern) (guard : d851 p = 1) : d512 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4161 (p : Pattern) (guard : d851 p = 1) : d513 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4162 (p : Pattern) (guard : d851 p = 1) : d514 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4160 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4161 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4163 (p : Pattern) (guard : d851 p = 1) : d515 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4162 p hg
    simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4164 (p : Pattern) (guard : d851 p = 1) : d516 p ≤ (0 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4156 p hg
    simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d516, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4165 (p : Pattern) (guard : d851 p = 1) : d517 p ≤ (0 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d517, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4166 (p : Pattern) (guard : d851 p = 1) : d518 p ≤ (0 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4164 p hg
    simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4165 p hg
    simpa only [d518, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4167 (p : Pattern) (guard : d851 p = 1) : d519 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d519, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4168 (p : Pattern) (guard : d851 p = 1) : d520 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d520, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4169 (p : Pattern) (guard : d851 p = 1) : d521 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4167 p hg
    simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4168 p hg
    simpa only [d521, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4170 (p : Pattern) (guard : d851 p = 1) : d522 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4168 p hg
    simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d522, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4171 (p : Pattern) (guard : d851 p = 1) : d523 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4169 p hg
    simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4170 p hg
    simpa only [d523, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4172 (p : Pattern) (guard : d851 p = 1) : d524 p ≤ (0 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4166 p hg
    simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4171 p hg
    simpa only [d524, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4173 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (8 : Int) + d7 p := by
  omega
theorem compare4174 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (8 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4175 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (8 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4173 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4176 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (8 : Int) + d55 p := by
  omega
theorem compare4177 (p : Pattern) (guard : d851 p = 1) : d137 p ≤ (8 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4178 (p : Pattern) (guard : d851 p = 1) : d501 p ≤ (8 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d501, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4179 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (8 : Int) + d11 p := by
  omega
theorem compare4180 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (8 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4181 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (8 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4179 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4180 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4182 (p : Pattern) (guard : d851 p = 1) : d502 p ≤ (8 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4183 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (8 : Int) + d60 p := by
  omega
theorem compare4184 (p : Pattern) (guard : d851 p = 1) : d143 p ≤ (8 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4183 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4185 (p : Pattern) (guard : d851 p = 1) : d144 p ≤ (8 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4184 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4186 (p : Pattern) (guard : d851 p = 1) : d503 p ≤ (8 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4185 p hg
    simpa only [d503, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4187 (p : Pattern) (guard : d851 p = 1) : d504 p ≤ (8 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4178 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d504, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4188 (p : Pattern) (guard : d851 p = 1) : d505 p ≤ (8 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4189 (p : Pattern) (guard : d851 p = 1) : d65 p ≤ (8 : Int) + d65 p := by
  omega
theorem compare4190 (p : Pattern) (guard : d851 p = 1) : d506 p ≤ (8 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4191 (p : Pattern) (guard : d851 p = 1) : d507 p ≤ (8 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4188 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4190 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4192 (p : Pattern) (guard : d851 p = 1) : d508 p ≤ (8 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4191 p hg
    simpa only [d508, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4193 (p : Pattern) (guard : d851 p = 1) : d509 p ≤ (8 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4178 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d509, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4194 (p : Pattern) (guard : d851 p = 1) : d510 p ≤ (8 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d510, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4195 (p : Pattern) (guard : d851 p = 1) : d511 p ≤ (8 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4193 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4194 p hg
    simpa only [d511, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4196 (p : Pattern) (guard : d851 p = 1) : d512 p ≤ (8 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4188 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4197 (p : Pattern) (guard : d851 p = 1) : d513 p ≤ (8 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4190 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4198 (p : Pattern) (guard : d851 p = 1) : d514 p ≤ (8 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4196 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4197 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4199 (p : Pattern) (guard : d851 p = 1) : d515 p ≤ (8 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4198 p hg
    simpa only [d515, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
