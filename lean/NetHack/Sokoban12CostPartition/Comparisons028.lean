/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3920 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3921 (p : Pattern) (guard : d829 p = 1) : d61 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3920 p hg
    simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3922 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3923 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3922 p hg
    simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3924 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3923 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3925 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3924 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3926 (p : Pattern) (guard : d829 p = 1) : d454 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3918 p hg
    simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3925 p hg
    simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3927 (p : Pattern) (guard : d829 p = 1) : d455 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3912 p hg
    simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3928 (p : Pattern) (guard : d829 p = 1) : d456 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3929 (p : Pattern) (guard : d829 p = 1) : d457 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3930 (p : Pattern) (guard : d829 p = 1) : d458 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3928 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3929 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3931 (p : Pattern) (guard : d829 p = 1) : d459 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3932 (p : Pattern) (guard : d829 p = 1) : d460 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3924 p hg
    simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3933 (p : Pattern) (guard : d829 p = 1) : d461 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3931 p hg
    simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3932 p hg
    simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3934 (p : Pattern) (guard : d829 p = 1) : d462 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3930 p hg
    simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3933 p hg
    simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3935 (p : Pattern) (guard : d829 p = 1) : d463 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3927 p hg
    simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3936 (p : Pattern) (guard : d829 p = 1) : d464 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3937 (p : Pattern) (guard : d829 p = 1) : d465 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3935 p hg
    simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3936 p hg
    simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3938 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3939 (p : Pattern) (guard : d829 p = 1) : d467 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3940 (p : Pattern) (guard : d829 p = 1) : d468 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3939 p hg
    simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3941 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3922 p hg
    simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3942 (p : Pattern) (guard : d829 p = 1) : d470 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3943 (p : Pattern) (guard : d829 p = 1) : d471 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3944 (p : Pattern) (guard : d829 p = 1) : d472 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3940 p hg
    simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3943 p hg
    simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3945 (p : Pattern) (guard : d829 p = 1) : d473 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3944 p hg
    simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3946 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3947 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3946 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3948 (p : Pattern) (guard : d829 p = 1) : d474 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3947 p hg
    simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3949 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3950 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3949 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3951 (p : Pattern) (guard : d829 p = 1) : d475 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3950 p hg
    simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3952 (p : Pattern) (guard : d829 p = 1) : d476 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3948 p hg
    simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3951 p hg
    simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3953 (p : Pattern) (guard : d829 p = 1) : d477 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3952 p hg
    simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3954 (p : Pattern) (guard : d829 p = 1) : d478 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3945 p hg
    simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3955 (p : Pattern) (guard : d829 p = 1) : d479 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3939 p hg
    simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3956 (p : Pattern) (guard : d829 p = 1) : d480 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3957 (p : Pattern) (guard : d829 p = 1) : d481 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3955 p hg
    simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3956 p hg
    simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3958 (p : Pattern) (guard : d829 p = 1) : d482 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3957 p hg
    simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3959 (p : Pattern) (guard : d829 p = 1) : d483 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3958 p hg
    simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3960 (p : Pattern) (guard : d829 p = 1) : d484 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3954 p hg
    simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3959 p hg
    simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3961 (p : Pattern) (guard : d829 p = 1) : d485 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3937 p hg
    simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3962 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (2 : Int) + d56 p := by
  omega
theorem compare3963 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3962 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3964 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (2 : Int) + d62 p := by
  omega
theorem compare3965 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3964 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3966 (p : Pattern) (guard : d829 p = 1) : d451 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d451, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3967 (p : Pattern) (guard : d829 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare3968 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d452, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3969 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d829, d56, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3970 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (2 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d452, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3971 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3968 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3970 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3972 (p : Pattern) (guard : d829 p = 1) : d452 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3968 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3971 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3973 (p : Pattern) (guard : d829 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare3974 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d453, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3975 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (2 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3976 (p : Pattern) (guard : d829 p = 1) : d61 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d829, d61, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3977 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d62, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3978 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d453, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3979 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3974 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3980 (p : Pattern) (guard : d829 p = 1) : d453 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3974 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3981 (p : Pattern) (guard : d829 p = 1) : d454 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3972 p hg
    simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3980 p hg
    simpa only [d454, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3982 (p : Pattern) (guard : d829 p = 1) : d455 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3966 p hg
    simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3981 p hg
    simpa only [d455, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3983 (p : Pattern) (guard : d829 p = 1) : d456 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d456, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3984 (p : Pattern) (guard : d829 p = 1) : d457 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d457, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3985 (p : Pattern) (guard : d829 p = 1) : d458 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d458, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3986 (p : Pattern) (guard : d829 p = 1) : d459 p ≤ (2 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3971 p hg
    simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d459, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3987 (p : Pattern) (guard : d829 p = 1) : d460 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d460, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3988 (p : Pattern) (guard : d829 p = 1) : d461 p ≤ (2 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d461, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3989 (p : Pattern) (guard : d829 p = 1) : d462 p ≤ (2 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3988 p hg
    simpa only [d462, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3990 (p : Pattern) (guard : d829 p = 1) : d463 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3989 p hg
    simpa only [d463, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3991 (p : Pattern) (guard : d829 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare3992 (p : Pattern) (guard : d829 p = 1) : d464 p ≤ (2 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3989 p hg
    simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d464, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3993 (p : Pattern) (guard : d829 p = 1) : d465 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d465, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3994 (p : Pattern) (guard : d829 p = 1) : d137 p ≤ (2 : Int) + d137 p := by
  omega
theorem compare3995 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (2 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3994 p hg
    simpa only [d466, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3996 (p : Pattern) (guard : d829 p = 1) : d467 p ≤ (2 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d467, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3997 (p : Pattern) (guard : d829 p = 1) : d468 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d468, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3998 (p : Pattern) (guard : d829 p = 1) : d144 p ≤ (2 : Int) + d144 p := by
  omega
theorem compare3999 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3998 p hg
    simpa only [d469, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4000 (p : Pattern) (guard : d829 p = 1) : d470 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d470, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4001 (p : Pattern) (guard : d829 p = 1) : d471 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4000 p hg
    simpa only [d471, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4002 (p : Pattern) (guard : d829 p = 1) : d472 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d472, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4003 (p : Pattern) (guard : d829 p = 1) : d473 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d473, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4004 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3994 p hg
    simpa only [d466, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4005 (p : Pattern) (guard : d829 p = 1) : d466 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4004 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4006 (p : Pattern) (guard : d829 p = 1) : d474 p ≤ (2 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4005 p hg
    simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d474, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4007 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3998 p hg
    simpa only [d469, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4008 (p : Pattern) (guard : d829 p = 1) : d469 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4007 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4009 (p : Pattern) (guard : d829 p = 1) : d475 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4008 p hg
    simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d475, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4010 (p : Pattern) (guard : d829 p = 1) : d476 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4006 p hg
    simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4009 p hg
    simpa only [d476, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4011 (p : Pattern) (guard : d829 p = 1) : d477 p ≤ (2 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d477, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4012 (p : Pattern) (guard : d829 p = 1) : d478 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4003 p hg
    simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4011 p hg
    simpa only [d478, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4013 (p : Pattern) (guard : d829 p = 1) : d479 p ≤ (2 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d479, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4014 (p : Pattern) (guard : d829 p = 1) : d480 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4000 p hg
    simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d480, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4015 (p : Pattern) (guard : d829 p = 1) : d481 p ≤ (2 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4013 p hg
    simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4014 p hg
    simpa only [d481, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4016 (p : Pattern) (guard : d829 p = 1) : d482 p ≤ (2 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4015 p hg
    simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d482, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4017 (p : Pattern) (guard : d829 p = 1) : d483 p ≤ (2 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d483, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4018 (p : Pattern) (guard : d829 p = 1) : d484 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4012 p hg
    simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4017 p hg
    simpa only [d484, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4019 (p : Pattern) (guard : d829 p = 1) : d485 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3993 p hg
    simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4018 p hg
    simpa only [d485, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4020 (p : Pattern) (guard : d1053 p = 1) : d56 p ≤ (0 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3914 p hg
    simpa only [d1053, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4021 (p : Pattern) (guard : d1053 p = 1) : d56 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4022 (p : Pattern) (guard : d1053 p = 1) : d61 p ≤ (0 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3920 p hg
    simpa only [d1053, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4023 (p : Pattern) (guard : d1053 p = 1) : d62 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d62, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d62, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d62, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4022 p hg
    simpa only [d62, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4024 (p : Pattern) (guard : d1053 p = 1) : d62 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4025 (p : Pattern) (guard : d1053 p = 1) : d451 p ≤ (0 : Int) + d504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d451, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d451, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d451, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d451, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4026 (p : Pattern) (guard : d1053 p = 1) : d452 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d452, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d452, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d452, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d452, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4027 (p : Pattern) (guard : d1053 p = 1) : d453 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d453, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d453, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d453, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d453, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4028 (p : Pattern) (guard : d1053 p = 1) : d454 p ≤ (0 : Int) + d507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d454, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4026 p hg
    simpa only [d454, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d454, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4027 p hg
    simpa only [d454, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4029 (p : Pattern) (guard : d1053 p = 1) : d455 p ≤ (0 : Int) + d508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d455, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4025 p hg
    simpa only [d455, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d455, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4028 p hg
    simpa only [d455, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4030 (p : Pattern) (guard : d1053 p = 1) : d456 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d456, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d456, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d456, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d456, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4031 (p : Pattern) (guard : d1053 p = 1) : d457 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d457, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d457, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d457, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d457, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4032 (p : Pattern) (guard : d1053 p = 1) : d458 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d458, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d458, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d458, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4031 p hg
    simpa only [d458, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4033 (p : Pattern) (guard : d1053 p = 1) : d459 p ≤ (0 : Int) + d512 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d459, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4026 p hg
    simpa only [d459, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d459, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d459, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4034 (p : Pattern) (guard : d1053 p = 1) : d460 p ≤ (0 : Int) + d513 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d460, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4027 p hg
    simpa only [d460, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d460, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d460, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4035 (p : Pattern) (guard : d1053 p = 1) : d461 p ≤ (0 : Int) + d514 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d461, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4033 p hg
    simpa only [d461, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d461, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4034 p hg
    simpa only [d461, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4036 (p : Pattern) (guard : d1053 p = 1) : d462 p ≤ (0 : Int) + d515 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d462, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4032 p hg
    simpa only [d462, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d462, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d462, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4037 (p : Pattern) (guard : d1053 p = 1) : d463 p ≤ (0 : Int) + d516 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d463, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d463, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d463, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d463, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4038 (p : Pattern) (guard : d1053 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare4039 (p : Pattern) (guard : d1053 p = 1) : d464 p ≤ (0 : Int) + d517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d464, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d464, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d464, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d464, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4040 (p : Pattern) (guard : d1053 p = 1) : d465 p ≤ (0 : Int) + d518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d465, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4037 p hg
    simpa only [d465, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d465, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4039 p hg
    simpa only [d465, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4041 (p : Pattern) (guard : d1053 p = 1) : d137 p ≤ (0 : Int) + d137 p := by
  omega
theorem compare4042 (p : Pattern) (guard : d1053 p = 1) : d466 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d466, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d466, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d466, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4041 p hg
    simpa only [d466, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4043 (p : Pattern) (guard : d1053 p = 1) : d467 p ≤ (0 : Int) + d501 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4042 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4044 (p : Pattern) (guard : d1053 p = 1) : d468 p ≤ (0 : Int) + d501 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4043 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4045 (p : Pattern) (guard : d1053 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare4046 (p : Pattern) (guard : d1053 p = 1) : d469 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d469, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d469, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d469, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4045 p hg
    simpa only [d469, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4047 (p : Pattern) (guard : d1053 p = 1) : d470 p ≤ (0 : Int) + d503 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4046 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4048 (p : Pattern) (guard : d1053 p = 1) : d471 p ≤ (0 : Int) + d503 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4049 (p : Pattern) (guard : d1053 p = 1) : d472 p ≤ (0 : Int) + d504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d472, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4044 p hg
    simpa only [d472, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d472, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4048 p hg
    simpa only [d472, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4050 (p : Pattern) (guard : d1053 p = 1) : d473 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d473, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4049 p hg
    simpa only [d473, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d473, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d473, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4051 (p : Pattern) (guard : d1053 p = 1) : d474 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d474, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4042 p hg
    simpa only [d474, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d474, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d474, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4052 (p : Pattern) (guard : d1053 p = 1) : d475 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d475, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4046 p hg
    simpa only [d475, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d475, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d475, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4053 (p : Pattern) (guard : d1053 p = 1) : d476 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d476, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d476, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d476, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d476, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4054 (p : Pattern) (guard : d1053 p = 1) : d477 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d477, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d477, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d477, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d477, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4055 (p : Pattern) (guard : d1053 p = 1) : d478 p ≤ (0 : Int) + d521 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d478, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4050 p hg
    simpa only [d478, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d478, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4054 p hg
    simpa only [d478, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4056 (p : Pattern) (guard : d1053 p = 1) : d479 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d479, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4043 p hg
    simpa only [d479, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d479, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d479, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4057 (p : Pattern) (guard : d1053 p = 1) : d480 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d480, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d480, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d480, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d480, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4058 (p : Pattern) (guard : d1053 p = 1) : d481 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d481, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4056 p hg
    simpa only [d481, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d481, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4057 p hg
    simpa only [d481, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4059 (p : Pattern) (guard : d1053 p = 1) : d482 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d482, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d482, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d482, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d482, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
