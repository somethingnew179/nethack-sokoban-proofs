/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3920 (p : Pattern) (guard : d0 p = 1) : d346 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3921 (p : Pattern) (guard : d1151 p = 1) : d347 p ≤ (2 : Int) + d16 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d1151, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3920 p hg
    simpa only [d1151, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3922 (p : Pattern) (guard : d1151 p = 1) : d348 p ≤ (2 : Int) + d16 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3923 (p : Pattern) (guard : d0 p = 1) : d349 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3924 (p : Pattern) (guard : d1151 p = 1) : d350 p ≤ (2 : Int) + d15 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3906 p hg
    simpa only [d1151, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3923 p hg
    simpa only [d1151, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3925 (p : Pattern) (guard : d0 p = 1) : d351 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3926 (p : Pattern) (guard : d1151 p = 1) : d352 p ≤ (2 : Int) + d53 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d1151, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3925 p hg
    simpa only [d1151, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3927 (p : Pattern) (guard : d1151 p = 1) : d353 p ≤ (2 : Int) + d1152 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d353, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3924 p hg
    simpa only [d353, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d353, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d353, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3928 (p : Pattern) (guard : d1151 p = 1) : d354 p ≤ (2 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d354, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3922 p hg
    simpa only [d354, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d354, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3927 p hg
    simpa only [d354, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3929 (p : Pattern) (guard : d1151 p = 1) : d355 p ≤ (2 : Int) + d1153 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3928 p hg
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3930 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3931 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (2 : Int) + d86 p := by
  omega
theorem compare3932 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3933 (p : Pattern) (guard : d915 p = 1) : d356 p ≤ (2 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3931 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3932 p hg
    simpa only [d915, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3934 (p : Pattern) (guard : d1150 p = 1) : d356 p ≤ (2 : Int) + d86 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3930 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3933 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3935 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3936 (p : Pattern) (guard : d1151 p = 1) : d359 p ≤ (2 : Int) + d86 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d1151, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3935 p hg
    simpa only [d1151, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3937 (p : Pattern) (guard : d1151 p = 1) : d360 p ≤ (2 : Int) + d1154 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d360, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3901 p hg
    simpa only [d360, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d360, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3936 p hg
    simpa only [d360, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3938 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3939 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (2 : Int) + d98 p := by
  omega
theorem compare3940 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3941 (p : Pattern) (guard : d915 p = 1) : d361 p ≤ (2 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3939 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3940 p hg
    simpa only [d915, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3942 (p : Pattern) (guard : d1150 p = 1) : d361 p ≤ (2 : Int) + d98 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3943 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3944 (p : Pattern) (guard : d1151 p = 1) : d363 p ≤ (2 : Int) + d98 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d1151, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3943 p hg
    simpa only [d1151, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3945 (p : Pattern) (guard : d1151 p = 1) : d364 p ≤ (2 : Int) + d1155 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d364, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3937 p hg
    simpa only [d364, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d364, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3944 p hg
    simpa only [d364, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3946 (p : Pattern) (guard : d0 p = 1) : d365 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3947 (p : Pattern) (guard : d1151 p = 1) : d366 p ≤ (2 : Int) + d86 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d1151, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3946 p hg
    simpa only [d1151, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3948 (p : Pattern) (guard : d1151 p = 1) : d367 p ≤ (2 : Int) + d1154 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d367, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d367, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d367, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3947 p hg
    simpa only [d367, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3949 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3950 (p : Pattern) (guard : d1151 p = 1) : d369 p ≤ (2 : Int) + d98 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d1151, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3949 p hg
    simpa only [d1151, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3951 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3952 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (2 : Int) + d97 p := by
  omega
theorem compare3953 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3954 (p : Pattern) (guard : d915 p = 1) : d370 p ≤ (2 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3952 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d915, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3955 (p : Pattern) (guard : d1150 p = 1) : d370 p ≤ (2 : Int) + d97 p := by
  cases selected : p 133 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3951 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d915 p = 1 := by simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3954 p hg
    simpa only [d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3956 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3957 (p : Pattern) (guard : d1151 p = 1) : d372 p ≤ (2 : Int) + d97 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3955 p hg
    simpa only [d1151, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3956 p hg
    simpa only [d1151, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3958 (p : Pattern) (guard : d1151 p = 1) : d373 p ≤ (2 : Int) + d1156 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d373, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3950 p hg
    simpa only [d373, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d373, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3957 p hg
    simpa only [d373, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3959 (p : Pattern) (guard : d1151 p = 1) : d374 p ≤ (2 : Int) + d1157 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d374, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3948 p hg
    simpa only [d374, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d374, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3958 p hg
    simpa only [d374, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3960 (p : Pattern) (guard : d1151 p = 1) : d375 p ≤ (2 : Int) + d1158 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d375, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3945 p hg
    simpa only [d375, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d375, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3959 p hg
    simpa only [d375, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3961 (p : Pattern) (guard : d1151 p = 1) : d376 p ≤ (2 : Int) + d1159 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d376, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3929 p hg
    simpa only [d376, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d376, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d376, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3962 (p : Pattern) (guard : d1151 p = 1) : d377 p ≤ (2 : Int) + d1153 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d377, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d377, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d377, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3927 p hg
    simpa only [d377, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3963 (p : Pattern) (guard : d1151 p = 1) : d378 p ≤ (2 : Int) + d1153 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3962 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3964 (p : Pattern) (guard : d0 p = 1) : d379 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3965 (p : Pattern) (guard : d1151 p = 1) : d380 p ≤ (2 : Int) + d97 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1151, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3955 p hg
    simpa only [d1151, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3964 p hg
    simpa only [d1151, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3966 (p : Pattern) (guard : d1151 p = 1) : d381 p ≤ (2 : Int) + d1156 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d381, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3944 p hg
    simpa only [d381, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d381, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d381, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3967 (p : Pattern) (guard : d1151 p = 1) : d382 p ≤ (2 : Int) + d1157 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d382, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3937 p hg
    simpa only [d382, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d382, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3966 p hg
    simpa only [d382, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3968 (p : Pattern) (guard : d1151 p = 1) : d383 p ≤ (2 : Int) + d1160 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d383, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d383, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d383, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d383, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3969 (p : Pattern) (guard : d1151 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare3970 (p : Pattern) (guard : d1151 p = 1) : d384 p ≤ (2 : Int) + d1161 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d384, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3957 p hg
    simpa only [d384, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d384, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d384, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3971 (p : Pattern) (guard : d1151 p = 1) : d385 p ≤ (2 : Int) + d1162 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d385, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3968 p hg
    simpa only [d385, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d385, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3970 p hg
    simpa only [d385, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3972 (p : Pattern) (guard : d1151 p = 1) : d386 p ≤ (2 : Int) + d1163 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d386, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d386, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d386, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3971 p hg
    simpa only [d386, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3973 (p : Pattern) (guard : d1151 p = 1) : d387 p ≤ (2 : Int) + d1164 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d387, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d387, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d387, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3972 p hg
    simpa only [d387, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3974 (p : Pattern) (guard : d1151 p = 1) : d388 p ≤ (2 : Int) + d1165 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d388, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d388, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1151 p = 1 := by simpa only [d388, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d388, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3975 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3976 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3977 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare3978 (p : Pattern) (guard : d985 p = 1) : d4 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3979 (p : Pattern) (guard : d985 p = 1) : d5 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d5, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3980 (p : Pattern) (guard : d985 p = 1) : d6 p ≤ (0 : Int) + d743 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d6, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d6, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d6, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d6, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3981 (p : Pattern) (guard : d985 p = 1) : d7 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d7, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3982 (p : Pattern) (guard : d985 p = 1) : d8 p ≤ (0 : Int) + d745 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d8, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3980 p hg
    simpa only [d8, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d8, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3981 p hg
    simpa only [d8, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3983 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3984 (p : Pattern) (guard : d985 p = 1) : d1 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3985 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare3986 (p : Pattern) (guard : d985 p = 1) : d10 p ≤ (0 : Int) + d9 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3987 (p : Pattern) (guard : d985 p = 1) : d11 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d11, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3988 (p : Pattern) (guard : d985 p = 1) : d12 p ≤ (0 : Int) + d746 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d12, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d12, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d12, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d12, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3989 (p : Pattern) (guard : d985 p = 1) : d13 p ≤ (0 : Int) + d747 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d13, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3990 (p : Pattern) (guard : d985 p = 1) : d14 p ≤ (0 : Int) + d748 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d14, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3988 p hg
    simpa only [d14, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d14, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3989 p hg
    simpa only [d14, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3991 (p : Pattern) (guard : d985 p = 1) : d15 p ≤ (0 : Int) + d749 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d15, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d15, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d15, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d15, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3992 (p : Pattern) (guard : d985 p = 1) : d16 p ≤ (0 : Int) + d750 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d16, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d16, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d16, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d16, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3993 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d750 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3994 (p : Pattern) (guard : d1249 p = 1) : d328 p ≤ (0 : Int) + d750 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3993 p hg
    simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3995 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3996 (p : Pattern) (guard : d1249 p = 1) : d328 p ≤ (0 : Int) + d755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d328, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d1249, d328, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d328, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d1249, d328, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3997 (p : Pattern) (guard : d1249 p = 1) : d328 p ≤ (0 : Int) + d756 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3994 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3998 (p : Pattern) (guard : d985 p = 1) : d37 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d37, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3999 (p : Pattern) (guard : d985 p = 1) : d38 p ≤ (0 : Int) + d751 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d38, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3980 p hg
    simpa only [d38, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d38, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3998 p hg
    simpa only [d38, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4000 (p : Pattern) (guard : d985 p = 1) : d39 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4001 (p : Pattern) (guard : d985 p = 1) : d40 p ≤ (0 : Int) + d752 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d40, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3988 p hg
    simpa only [d40, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d40, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4000 p hg
    simpa only [d40, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4002 (p : Pattern) (guard : d985 p = 1) : d41 p ≤ (0 : Int) + d753 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d41, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d41, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d41, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d41, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4003 (p : Pattern) (guard : d985 p = 1) : d42 p ≤ (0 : Int) + d754 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d42, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d42, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d42, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d42, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4004 (p : Pattern) (guard : d1249 p = 1) : d329 p ≤ (0 : Int) + d754 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4003 p hg
    simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4005 (p : Pattern) (guard : d1249 p = 1) : d330 p ≤ (0 : Int) + d757 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d330, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d330, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d330, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4004 p hg
    simpa only [d330, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4006 (p : Pattern) (guard : d1249 p = 1) : d331 p ≤ (0 : Int) + d758 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d331, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d331, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d331, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4005 p hg
    simpa only [d331, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4007 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4008 (p : Pattern) (guard : d1249 p = 1) : d332 p ≤ (0 : Int) + d749 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4007 p hg
    simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4009 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4010 (p : Pattern) (guard : d1249 p = 1) : d332 p ≤ (0 : Int) + d759 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d332, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d1249, d332, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d332, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4009 p hg
    simpa only [d1249, d332, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4011 (p : Pattern) (guard : d1249 p = 1) : d332 p ≤ (0 : Int) + d760 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4008 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4012 (p : Pattern) (guard : d1249 p = 1) : d333 p ≤ (0 : Int) + d753 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4009 p hg
    simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4013 (p : Pattern) (guard : d1249 p = 1) : d334 p ≤ (0 : Int) + d761 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d334, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d334, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d334, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4012 p hg
    simpa only [d334, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4014 (p : Pattern) (guard : d1249 p = 1) : d335 p ≤ (0 : Int) + d762 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d335, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4011 p hg
    simpa only [d335, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d335, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4013 p hg
    simpa only [d335, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4015 (p : Pattern) (guard : d985 p = 1) : d52 p ≤ (0 : Int) + d763 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d52, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d52, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d52, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d52, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4016 (p : Pattern) (guard : d985 p = 1) : d53 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d53, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d53, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d53, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4015 p hg
    simpa only [d53, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4017 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4018 (p : Pattern) (guard : d1249 p = 1) : d336 p ≤ (0 : Int) + d764 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4017 p hg
    simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4019 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4020 (p : Pattern) (guard : d1249 p = 1) : d336 p ≤ (0 : Int) + d767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d336, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d1249, d336, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d336, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4019 p hg
    simpa only [d1249, d336, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4021 (p : Pattern) (guard : d1249 p = 1) : d336 p ≤ (0 : Int) + d768 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4018 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4022 (p : Pattern) (guard : d985 p = 1) : d61 p ≤ (0 : Int) + d765 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d61, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d61, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d61, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d61, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4023 (p : Pattern) (guard : d985 p = 1) : d62 p ≤ (0 : Int) + d766 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d62, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d62, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d62, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4022 p hg
    simpa only [d62, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4024 (p : Pattern) (guard : d1249 p = 1) : d337 p ≤ (0 : Int) + d766 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4019 p hg
    simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4025 (p : Pattern) (guard : d1249 p = 1) : d338 p ≤ (0 : Int) + d769 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d338, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d338, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d338, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d338, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4026 (p : Pattern) (guard : d1249 p = 1) : d339 p ≤ (0 : Int) + d770 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d339, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d339, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d339, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4025 p hg
    simpa only [d339, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4027 (p : Pattern) (guard : d1249 p = 1) : d340 p ≤ (0 : Int) + d771 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d340, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4014 p hg
    simpa only [d340, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d340, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4026 p hg
    simpa only [d340, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4028 (p : Pattern) (guard : d1249 p = 1) : d341 p ≤ (0 : Int) + d772 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d341, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4006 p hg
    simpa only [d341, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d341, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4027 p hg
    simpa only [d341, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4029 (p : Pattern) (guard : d985 p = 1) : d68 p ≤ (0 : Int) + d773 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d68, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d68, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d68, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d68, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4030 (p : Pattern) (guard : d985 p = 1) : d69 p ≤ (0 : Int) + d774 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d69, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d69, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d69, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d69, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4031 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4032 (p : Pattern) (guard : d1249 p = 1) : d342 p ≤ (0 : Int) + d774 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4031 p hg
    simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4033 (p : Pattern) (guard : d1249 p = 1) : d343 p ≤ (0 : Int) + d775 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d343, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d343, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d343, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4032 p hg
    simpa only [d343, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4034 (p : Pattern) (guard : d1249 p = 1) : d344 p ≤ (0 : Int) + d776 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d344, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d344, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d344, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4033 p hg
    simpa only [d344, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4035 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4036 (p : Pattern) (guard : d1249 p = 1) : d345 p ≤ (0 : Int) + d773 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4037 (p : Pattern) (guard : d1249 p = 1) : d346 p ≤ (0 : Int) + d777 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d346, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d346, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d346, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d346, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4038 (p : Pattern) (guard : d1249 p = 1) : d347 p ≤ (0 : Int) + d778 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d347, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d347, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d347, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4037 p hg
    simpa only [d347, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4039 (p : Pattern) (guard : d1249 p = 1) : d348 p ≤ (0 : Int) + d779 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d348, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4034 p hg
    simpa only [d348, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d348, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d348, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4040 (p : Pattern) (guard : d1249 p = 1) : d349 p ≤ (0 : Int) + d780 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d349, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d349, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d349, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d349, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4041 (p : Pattern) (guard : d1249 p = 1) : d350 p ≤ (0 : Int) + d781 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d350, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4011 p hg
    simpa only [d350, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d350, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4040 p hg
    simpa only [d350, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4042 (p : Pattern) (guard : d1249 p = 1) : d351 p ≤ (0 : Int) + d782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d351, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4020 p hg
    simpa only [d351, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d351, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d351, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4043 (p : Pattern) (guard : d1249 p = 1) : d352 p ≤ (0 : Int) + d783 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d352, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d352, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d352, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4042 p hg
    simpa only [d352, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4044 (p : Pattern) (guard : d1249 p = 1) : d353 p ≤ (0 : Int) + d784 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4041 p hg
    simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4043 p hg
    simpa only [d353, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4045 (p : Pattern) (guard : d1249 p = 1) : d354 p ≤ (0 : Int) + d785 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4039 p hg
    simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4044 p hg
    simpa only [d354, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4046 (p : Pattern) (guard : d1249 p = 1) : d355 p ≤ (0 : Int) + d786 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4028 p hg
    simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4045 p hg
    simpa only [d355, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4047 (p : Pattern) (guard : d985 p = 1) : d86 p ≤ (0 : Int) + d787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d86, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d86, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d86, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4015 p hg
    simpa only [d86, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4048 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d787 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4049 (p : Pattern) (guard : d1249 p = 1) : d356 p ≤ (0 : Int) + d787 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4048 p hg
    simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4050 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4051 (p : Pattern) (guard : d1249 p = 1) : d356 p ≤ (0 : Int) + d789 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d356, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d1249, d356, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d356, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4050 p hg
    simpa only [d1249, d356, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4052 (p : Pattern) (guard : d1249 p = 1) : d356 p ≤ (0 : Int) + d790 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4049 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4053 (p : Pattern) (guard : d985 p = 1) : d92 p ≤ (0 : Int) + d788 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d92, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d92, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d92, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4022 p hg
    simpa only [d92, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4054 (p : Pattern) (guard : d1249 p = 1) : d357 p ≤ (0 : Int) + d788 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4050 p hg
    simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4055 (p : Pattern) (guard : d1249 p = 1) : d358 p ≤ (0 : Int) + d791 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d358, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d358, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d358, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4054 p hg
    simpa only [d358, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4056 (p : Pattern) (guard : d1249 p = 1) : d359 p ≤ (0 : Int) + d792 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d359, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d359, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d359, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4055 p hg
    simpa only [d359, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4057 (p : Pattern) (guard : d1249 p = 1) : d360 p ≤ (0 : Int) + d793 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d360, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4006 p hg
    simpa only [d360, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d360, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4056 p hg
    simpa only [d360, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4058 (p : Pattern) (guard : d985 p = 1) : d97 p ≤ (0 : Int) + d794 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4059 (p : Pattern) (guard : d985 p = 1) : d98 p ≤ (0 : Int) + d795 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
