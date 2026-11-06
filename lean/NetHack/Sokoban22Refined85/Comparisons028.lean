/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3920 (p : Pattern) (guard : d4304 p = 1) : d656 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d656, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d656, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d656, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d4304, d656, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3921 (p : Pattern) (guard : d4147 p = 1) : d89 p ≤ (4 : Int) + d26 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3883 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d4147, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3922 (p : Pattern) (guard : d4147 p = 1) : d90 p ≤ (4 : Int) + d4324 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d90, d4324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d90, d4324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d90, d4324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d90, d4324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3923 (p : Pattern) (guard : d4147 p = 1) : d91 p ≤ (4 : Int) + d4160 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3924 (p : Pattern) (guard : d4147 p = 1) : d92 p ≤ (4 : Int) + d4325 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d92, d4325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3922 p hg
    simpa only [d92, d4325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d92, d4325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3923 p hg
    simpa only [d92, d4325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3925 (p : Pattern) (guard : d4147 p = 1) : d93 p ≤ (4 : Int) + d4161 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3923 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3926 (p : Pattern) (guard : d4147 p = 1) : d94 p ≤ (4 : Int) + d4326 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d94, d4326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3924 p hg
    simpa only [d94, d4326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d94, d4326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3925 p hg
    simpa only [d94, d4326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3927 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (4 : Int) + d4162 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3928 (p : Pattern) (guard : d4304 p = 1) : d657 p ≤ (4 : Int) + d4327 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d657, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d4304, d657, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d657, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3927 p hg
    simpa only [d4304, d657, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3929 (p : Pattern) (guard : d4304 p = 1) : d658 p ≤ (4 : Int) + d4328 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d658, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3920 p hg
    simpa only [d658, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d658, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3928 p hg
    simpa only [d658, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3930 (p : Pattern) (guard : d4304 p = 1) : d659 p ≤ (4 : Int) + d4329 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d659, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3918 p hg
    simpa only [d659, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d659, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3929 p hg
    simpa only [d659, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3931 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (4 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3932 (p : Pattern) (guard : d4304 p = 1) : d660 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d660, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d4304, d660, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d660, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3931 p hg
    simpa only [d4304, d660, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3933 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3934 (p : Pattern) (guard : d4304 p = 1) : d661 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d661, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d661, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d661, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3933 p hg
    simpa only [d4304, d661, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3935 (p : Pattern) (guard : d4304 p = 1) : d662 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d662, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3932 p hg
    simpa only [d662, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d662, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d662, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3936 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3937 (p : Pattern) (guard : d4304 p = 1) : d663 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d663, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d663, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d663, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3936 p hg
    simpa only [d4304, d663, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3938 (p : Pattern) (guard : d4304 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare3939 (p : Pattern) (guard : d4304 p = 1) : d664 p ≤ (4 : Int) + d4330 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d664, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3937 p hg
    simpa only [d664, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d664, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d664, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3940 (p : Pattern) (guard : d4304 p = 1) : d665 p ≤ (4 : Int) + d4331 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d665, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3935 p hg
    simpa only [d665, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d665, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3939 p hg
    simpa only [d665, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3941 (p : Pattern) (guard : d4304 p = 1) : d666 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d666, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3930 p hg
    simpa only [d666, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d666, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3940 p hg
    simpa only [d666, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3942 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (4 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3943 (p : Pattern) (guard : d4304 p = 1) : d667 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d667, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d4304, d667, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d667, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d4304, d667, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3944 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3945 (p : Pattern) (guard : d4304 p = 1) : d668 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d668, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d668, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d668, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3944 p hg
    simpa only [d4304, d668, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3946 (p : Pattern) (guard : d4304 p = 1) : d669 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d669, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3943 p hg
    simpa only [d669, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d669, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3945 p hg
    simpa only [d669, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3947 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d4162 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3948 (p : Pattern) (guard : d4304 p = 1) : d670 p ≤ (4 : Int) + d4327 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d670, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d4304, d670, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d670, d4327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3947 p hg
    simpa only [d4304, d670, d4327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3949 (p : Pattern) (guard : d4304 p = 1) : d671 p ≤ (4 : Int) + d4328 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d671, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d671, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d671, d4328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3948 p hg
    simpa only [d671, d4328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3950 (p : Pattern) (guard : d4304 p = 1) : d672 p ≤ (4 : Int) + d4329 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d672, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3946 p hg
    simpa only [d672, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d672, d4329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3949 p hg
    simpa only [d672, d4329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3951 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (4 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3952 (p : Pattern) (guard : d4304 p = 1) : d673 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d673, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d4304, d673, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d673, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3951 p hg
    simpa only [d4304, d673, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3953 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3954 (p : Pattern) (guard : d4304 p = 1) : d674 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d674, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d674, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d674, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d4304, d674, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3955 (p : Pattern) (guard : d4304 p = 1) : d675 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d675, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3952 p hg
    simpa only [d675, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d675, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3954 p hg
    simpa only [d675, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3956 (p : Pattern) (guard : d4304 p = 1) : d676 p ≤ (4 : Int) + d4330 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d676, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d676, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d676, d4330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d676, d4330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3957 (p : Pattern) (guard : d4304 p = 1) : d677 p ≤ (4 : Int) + d4331 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d677, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3955 p hg
    simpa only [d677, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d677, d4331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3956 p hg
    simpa only [d677, d4331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3958 (p : Pattern) (guard : d4304 p = 1) : d678 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d678, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3950 p hg
    simpa only [d678, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d678, d4332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3957 p hg
    simpa only [d678, d4332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3959 (p : Pattern) (guard : d4304 p = 1) : d679 p ≤ (4 : Int) + d4332 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3958 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3960 (p : Pattern) (guard : d4147 p = 1) : d105 p ≤ (4 : Int) + d105 p := by
  omega
theorem compare3961 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (4 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3962 (p : Pattern) (guard : d4147 p = 1) : d110 p ≤ (4 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2726 p hg
    simpa only [d4147, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3963 (p : Pattern) (guard : d4147 p = 1) : d111 p ≤ (4 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3962 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3964 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (4 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3965 (p : Pattern) (guard : d4147 p = 1) : d112 p ≤ (4 : Int) + d60 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3964 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3966 (p : Pattern) (guard : d4147 p = 1) : d113 p ≤ (4 : Int) + d4333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d113, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3962 p hg
    simpa only [d113, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d113, d4333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d113, d4333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3967 (p : Pattern) (guard : d4147 p = 1) : d114 p ≤ (4 : Int) + d4334 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d114, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d114, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d114, d4334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3966 p hg
    simpa only [d114, d4334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3968 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (4 : Int) + d118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3969 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (4 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d122, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d122, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3970 (p : Pattern) (guard : d4147 p = 1) : d123 p ≤ (4 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3968 p hg
    simpa only [d4147, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d4147, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3971 (p : Pattern) (guard : d0 p = 1) : d124 p ≤ (4 : Int) + d124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3972 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (4 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d125, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d125, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3973 (p : Pattern) (guard : d4147 p = 1) : d126 p ≤ (4 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3971 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3972 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3974 (p : Pattern) (guard : d4147 p = 1) : d127 p ≤ (4 : Int) + d4335 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d127, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3970 p hg
    simpa only [d127, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d127, d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d127, d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3975 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (4 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3976 (p : Pattern) (guard : d4147 p = 1) : d128 p ≤ (4 : Int) + d70 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d4147, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3977 (p : Pattern) (guard : d4147 p = 1) : d129 p ≤ (4 : Int) + d4336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d129, d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d129, d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d129, d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d129, d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3978 (p : Pattern) (guard : d4147 p = 1) : d130 p ≤ (4 : Int) + d4337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d130, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3974 p hg
    simpa only [d130, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d130, d4337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d130, d4337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3979 (p : Pattern) (guard : d4147 p = 1) : d131 p ≤ (4 : Int) + d4338 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d131, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d131, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d131, d4338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d131, d4338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3980 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (4 : Int) + d4344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3981 (p : Pattern) (guard : d4304 p = 1) : d680 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d680, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d4304, d680, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d680, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3980 p hg
    simpa only [d4304, d680, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3982 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (4 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3983 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (4 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d148, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d148, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3984 (p : Pattern) (guard : d4147 p = 1) : d149 p ≤ (4 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d4147, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d4147, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3985 (p : Pattern) (guard : d4147 p = 1) : d150 p ≤ (4 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d150, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3986 (p : Pattern) (guard : d4147 p = 1) : d151 p ≤ (4 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d151, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3987 (p : Pattern) (guard : d4147 p = 1) : d152 p ≤ (4 : Int) + d4346 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d152, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d152, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d152, d4346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d152, d4346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3988 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3989 (p : Pattern) (guard : d4304 p = 1) : d681 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d681, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d681, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d681, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3988 p hg
    simpa only [d4304, d681, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3990 (p : Pattern) (guard : d4304 p = 1) : d682 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d682, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3981 p hg
    simpa only [d682, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d682, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3989 p hg
    simpa only [d682, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3991 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3992 (p : Pattern) (guard : d4304 p = 1) : d683 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d683, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d683, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d683, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d4304, d683, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3993 (p : Pattern) (guard : d4147 p = 1) : d159 p ≤ (4 : Int) + d4350 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d159, d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3994 (p : Pattern) (guard : d4147 p = 1) : d160 p ≤ (4 : Int) + d4351 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3993 p hg
    simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d160, d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3995 (p : Pattern) (guard : d4147 p = 1) : d161 p ≤ (4 : Int) + d4352 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3994 p hg
    simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d161, d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3996 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3997 (p : Pattern) (guard : d4304 p = 1) : d162 p ≤ (4 : Int) + d4353 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d4304, d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d4304, d162, d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3998 (p : Pattern) (guard : d4304 p = 1) : d684 p ≤ (4 : Int) + d4354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d684, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d684, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d684, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d684, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3999 (p : Pattern) (guard : d4304 p = 1) : d685 p ≤ (4 : Int) + d4355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d685, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d685, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d685, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3998 p hg
    simpa only [d685, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4000 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (4 : Int) + d4344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4001 (p : Pattern) (guard : d4304 p = 1) : d686 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d686, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d4304, d686, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d686, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4000 p hg
    simpa only [d4304, d686, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4002 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4003 (p : Pattern) (guard : d4304 p = 1) : d687 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d687, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d687, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d687, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d4304, d687, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4004 (p : Pattern) (guard : d4304 p = 1) : d688 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d688, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4001 p hg
    simpa only [d688, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d688, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4003 p hg
    simpa only [d688, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4005 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4006 (p : Pattern) (guard : d4304 p = 1) : d689 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d689, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d689, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d689, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4005 p hg
    simpa only [d4304, d689, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4007 (p : Pattern) (guard : d4304 p = 1) : d690 p ≤ (4 : Int) + d4356 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d690, d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4006 p hg
    simpa only [d690, d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d690, d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d690, d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4008 (p : Pattern) (guard : d4304 p = 1) : d691 p ≤ (4 : Int) + d4357 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d691, d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4004 p hg
    simpa only [d691, d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d691, d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4007 p hg
    simpa only [d691, d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4009 (p : Pattern) (guard : d4304 p = 1) : d692 p ≤ (4 : Int) + d4358 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d692, d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3999 p hg
    simpa only [d692, d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d692, d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4008 p hg
    simpa only [d692, d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4010 (p : Pattern) (guard : d4304 p = 1) : d693 p ≤ (4 : Int) + d4359 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d693, d4359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d693, d4359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d693, d4359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4009 p hg
    simpa only [d693, d4359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4011 (p : Pattern) (guard : d4304 p = 1) : d694 p ≤ (4 : Int) + d4360 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d694, d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3959 p hg
    simpa only [d694, d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d694, d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4010 p hg
    simpa only [d694, d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4012 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (4 : Int) + d4362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4013 (p : Pattern) (guard : d4304 p = 1) : d674 p ≤ (4 : Int) + d4363 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d674, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d674, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d674, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4012 p hg
    simpa only [d4304, d674, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4014 (p : Pattern) (guard : d4304 p = 1) : d675 p ≤ (4 : Int) + d4364 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d675, d4364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3952 p hg
    simpa only [d675, d4364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d675, d4364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4013 p hg
    simpa only [d675, d4364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4015 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (4 : Int) + d4362 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4016 (p : Pattern) (guard : d4304 p = 1) : d661 p ≤ (4 : Int) + d4363 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d661, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d661, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d661, d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4015 p hg
    simpa only [d4304, d661, d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4017 (p : Pattern) (guard : d4304 p = 1) : d676 p ≤ (4 : Int) + d4365 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d676, d4365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d676, d4365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d676, d4365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d676, d4365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4018 (p : Pattern) (guard : d4304 p = 1) : d677 p ≤ (4 : Int) + d4366 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d677, d4366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4014 p hg
    simpa only [d677, d4366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d677, d4366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4017 p hg
    simpa only [d677, d4366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4019 (p : Pattern) (guard : d4304 p = 1) : d678 p ≤ (4 : Int) + d4367 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d678, d4367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3950 p hg
    simpa only [d678, d4367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d678, d4367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4018 p hg
    simpa only [d678, d4367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4020 (p : Pattern) (guard : d4304 p = 1) : d679 p ≤ (4 : Int) + d4368 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d679, d4368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d679, d4368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d679, d4368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4019 p hg
    simpa only [d679, d4368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4021 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (4 : Int) + d4344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4022 (p : Pattern) (guard : d4304 p = 1) : d695 p ≤ (4 : Int) + d4345 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d695, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d4304, d695, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d695, d4345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4021 p hg
    simpa only [d4304, d695, d4345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4023 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4024 (p : Pattern) (guard : d4304 p = 1) : d696 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d696, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d696, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d696, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d4304, d696, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4025 (p : Pattern) (guard : d4304 p = 1) : d697 p ≤ (4 : Int) + d4349 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d697, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4022 p hg
    simpa only [d697, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d697, d4349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4024 p hg
    simpa only [d697, d4349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4026 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (4 : Int) + d4347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4027 (p : Pattern) (guard : d4304 p = 1) : d698 p ≤ (4 : Int) + d4348 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d698, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d4304, d698, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d698, d4348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4026 p hg
    simpa only [d4304, d698, d4348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4028 (p : Pattern) (guard : d4304 p = 1) : d699 p ≤ (4 : Int) + d4354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d699, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4027 p hg
    simpa only [d699, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d699, d4354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d699, d4354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4029 (p : Pattern) (guard : d4304 p = 1) : d700 p ≤ (4 : Int) + d4355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d700, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4025 p hg
    simpa only [d700, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d700, d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4028 p hg
    simpa only [d700, d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4030 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (4 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4031 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (4 : Int) + d268 p := by
  omega
theorem compare4032 (p : Pattern) (guard : d1 p = 1) : d270 p ≤ (4 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d270, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4031 p hg
    simpa only [d270, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d270, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d270, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4033 (p : Pattern) (guard : d4147 p = 1) : d271 p ≤ (4 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d4147, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4032 p hg
    simpa only [d4147, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4034 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (4 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4035 (p : Pattern) (guard : d4147 p = 1) : d275 p ≤ (4 : Int) + d272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4034 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2742 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4036 (p : Pattern) (guard : d4147 p = 1) : d276 p ≤ (4 : Int) + d4369 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d276, d4369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4033 p hg
    simpa only [d276, d4369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d276, d4369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d276, d4369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4037 (p : Pattern) (guard : d0 p = 1) : d277 p ≤ (4 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4038 (p : Pattern) (guard : d4147 p = 1) : d278 p ≤ (4 : Int) + d277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4037 p hg
    simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2744 p hg
    simpa only [d4147, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4039 (p : Pattern) (guard : d4147 p = 1) : d279 p ≤ (4 : Int) + d4370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d279, d4370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d279, d4370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d279, d4370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d279, d4370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4040 (p : Pattern) (guard : d4147 p = 1) : d280 p ≤ (4 : Int) + d4371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d280, d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d280, d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d280, d4371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4039 p hg
    simpa only [d280, d4371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4041 (p : Pattern) (guard : d4147 p = 1) : d281 p ≤ (4 : Int) + d4372 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d281, d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d281, d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d281, d4372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4040 p hg
    simpa only [d281, d4372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4042 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (4 : Int) + d4376 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4043 (p : Pattern) (guard : d4304 p = 1) : d701 p ≤ (4 : Int) + d4377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d701, d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4041 p hg
    simpa only [d4304, d701, d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d701, d4377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4042 p hg
    simpa only [d4304, d701, d4377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4044 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (4 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4045 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4044 p hg
    simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d269, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4046 (p : Pattern) (guard : d4147 p = 1) : d291 p ≤ (4 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4045 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4047 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (4 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d292, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2741 p hg
    simpa only [d292, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d292, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d292, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4048 (p : Pattern) (guard : d4147 p = 1) : d293 p ≤ (4 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d4147, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4049 (p : Pattern) (guard : d4147 p = 1) : d294 p ≤ (4 : Int) + d4378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d294, d4378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4046 p hg
    simpa only [d294, d4378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d294, d4378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4048 p hg
    simpa only [d294, d4378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4050 (p : Pattern) (guard : d4147 p = 1) : d295 p ≤ (4 : Int) + d4379 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d295, d4379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4048 p hg
    simpa only [d295, d4379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d295, d4379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d295, d4379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4051 (p : Pattern) (guard : d4147 p = 1) : d296 p ≤ (4 : Int) + d4380 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d296, d4380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4049 p hg
    simpa only [d296, d4380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d296, d4380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4050 p hg
    simpa only [d296, d4380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4052 (p : Pattern) (guard : d4147 p = 1) : d297 p ≤ (4 : Int) + d4381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d297, d4381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d297, d4381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d297, d4381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d297, d4381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4053 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d4385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4054 (p : Pattern) (guard : d4304 p = 1) : d702 p ≤ (4 : Int) + d4386 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d702, d4386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d4304, d702, d4386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d702, d4386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d4304, d702, d4386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4055 (p : Pattern) (guard : d4304 p = 1) : d703 p ≤ (4 : Int) + d4387 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d703, d4387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4043 p hg
    simpa only [d703, d4387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d703, d4387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4054 p hg
    simpa only [d703, d4387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4056 (p : Pattern) (guard : d4304 p = 1) : d704 p ≤ (4 : Int) + d4388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d704, d4388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4054 p hg
    simpa only [d704, d4388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d704, d4388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d704, d4388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4057 (p : Pattern) (guard : d4304 p = 1) : d705 p ≤ (4 : Int) + d4389 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d705, d4389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4055 p hg
    simpa only [d705, d4389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d705, d4389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4056 p hg
    simpa only [d705, d4389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4058 (p : Pattern) (guard : d4304 p = 1) : d706 p ≤ (4 : Int) + d4390 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d706, d4390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d706, d4390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d706, d4390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4057 p hg
    simpa only [d706, d4390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4059 (p : Pattern) (guard : d4304 p = 1) : d707 p ≤ (4 : Int) + d4391 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d707, d4391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d707, d4391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d707, d4391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d707, d4391, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
