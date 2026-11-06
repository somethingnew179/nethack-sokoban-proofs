/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20020 (p : Pattern) (guard : d5849 p = 1) : d2249 p ≤ (0 : Int) + d3649 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2249, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d2249, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2249, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20019 p hg
    simpa only [d2249, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20021 (p : Pattern) (guard : d5849 p = 1) : d2250 p ≤ (0 : Int) + d3650 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2250, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20009 p hg
    simpa only [d2250, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2250, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2250, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20022 (p : Pattern) (guard : d5849 p = 1) : d2251 p ≤ (0 : Int) + d3651 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2251, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20021 p hg
    simpa only [d2251, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2251, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2251, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20023 (p : Pattern) (guard : d5849 p = 1) : d2252 p ≤ (0 : Int) + d3652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2252, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20020 p hg
    simpa only [d2252, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2252, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20022 p hg
    simpa only [d2252, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20024 (p : Pattern) (guard : d5849 p = 1) : d2253 p ≤ (0 : Int) + d3653 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2253, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20018 p hg
    simpa only [d2253, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2253, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20023 p hg
    simpa only [d2253, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20025 (p : Pattern) (guard : d5849 p = 1) : d2254 p ≤ (0 : Int) + d3654 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2254, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20013 p hg
    simpa only [d2254, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2254, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20024 p hg
    simpa only [d2254, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20026 (p : Pattern) (guard : d5849 p = 1) : d2255 p ≤ (0 : Int) + d3655 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2255, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19961 p hg
    simpa only [d2255, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2255, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20025 p hg
    simpa only [d2255, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20027 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20028 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3657 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19911 p hg
    simpa only [d5849, d2185, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20027 p hg
    simpa only [d5849, d2185, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20029 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3658 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19883 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20028 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20030 (p : Pattern) (guard : d5849 p = 1) : d2187 p ≤ (0 : Int) + d3659 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2187, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2187, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20031 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20029 p hg
    simpa only [d2201, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20030 p hg
    simpa only [d2201, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20032 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20033 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3663 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19911 p hg
    simpa only [d5849, d2185, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20032 p hg
    simpa only [d5849, d2185, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20034 (p : Pattern) (guard : d5849 p = 1) : d2187 p ≤ (0 : Int) + d3664 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20033 p hg
    simpa only [d2187, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2187, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20035 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3665 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2201, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20034 p hg
    simpa only [d2201, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20036 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20031 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20035 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20037 (p : Pattern) (guard : d5849 p = 1) : d2187 p ≤ (0 : Int) + d3667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d2187, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2187, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20038 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2201, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20037 p hg
    simpa only [d2201, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20039 (p : Pattern) (guard : d5849 p = 1) : d2197 p ≤ (0 : Int) + d3669 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19950 p hg
    simpa only [d2197, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2197, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20040 (p : Pattern) (guard : d5849 p = 1) : d2198 p ≤ (0 : Int) + d3670 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19951 p hg
    simpa only [d2198, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20039 p hg
    simpa only [d2198, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20041 (p : Pattern) (guard : d5849 p = 1) : d2202 p ≤ (0 : Int) + d3671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20038 p hg
    simpa only [d2202, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d2202, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20042 (p : Pattern) (guard : d5849 p = 1) : d2256 p ≤ (0 : Int) + d3672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2256, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20036 p hg
    simpa only [d2256, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2256, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20041 p hg
    simpa only [d2256, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20043 (p : Pattern) (guard : d5849 p = 1) : d2204 p ≤ (0 : Int) + d3673 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2204, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19897 p hg
    simpa only [d2204, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2204, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2204, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20044 (p : Pattern) (guard : d5849 p = 1) : d2205 p ≤ (0 : Int) + d3674 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2205, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19898 p hg
    simpa only [d2205, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2205, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20043 p hg
    simpa only [d2205, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20045 (p : Pattern) (guard : d5849 p = 1) : d2206 p ≤ (0 : Int) + d3675 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2206, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2206, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2206, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2206, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20046 (p : Pattern) (guard : d5849 p = 1) : d2207 p ≤ (0 : Int) + d3676 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20041 p hg
    simpa only [d2207, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20045 p hg
    simpa only [d2207, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20047 (p : Pattern) (guard : d5849 p = 1) : d2257 p ≤ (0 : Int) + d3677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2257, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20042 p hg
    simpa only [d2257, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2257, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20046 p hg
    simpa only [d2257, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20048 (p : Pattern) (guard : d5849 p = 1) : d2232 p ≤ (0 : Int) + d3678 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d2232, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19924 p hg
    simpa only [d2232, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20049 (p : Pattern) (guard : d5847 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14568 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20050 (p : Pattern) (guard : d5848 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20049 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20051 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20052 (p : Pattern) (guard : d5849 p = 1) : d2212 p ≤ (0 : Int) + d34 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20050 p hg
    simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20053 (p : Pattern) (guard : d5849 p = 1) : d2212 p ≤ (0 : Int) + d3679 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20052 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20054 (p : Pattern) (guard : d5849 p = 1) : d2258 p ≤ (0 : Int) + d3680 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2258, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20053 p hg
    simpa only [d2258, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2258, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19934 p hg
    simpa only [d2258, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20055 (p : Pattern) (guard : d5849 p = 1) : d2259 p ≤ (0 : Int) + d3681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2259, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20048 p hg
    simpa only [d2259, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2259, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20054 p hg
    simpa only [d2259, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20056 (p : Pattern) (guard : d5849 p = 1) : d2260 p ≤ (0 : Int) + d3682 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2260, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20055 p hg
    simpa only [d2260, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2260, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2260, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20057 (p : Pattern) (guard : d5849 p = 1) : d2261 p ≤ (0 : Int) + d3683 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2261, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20056 p hg
    simpa only [d2261, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2261, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2261, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20058 (p : Pattern) (guard : d5849 p = 1) : d2262 p ≤ (0 : Int) + d3684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2262, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20047 p hg
    simpa only [d2262, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2262, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20057 p hg
    simpa only [d2262, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20059 (p : Pattern) (guard : d5849 p = 1) : d2263 p ≤ (0 : Int) + d3685 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20035 p hg
    simpa only [d2263, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20048 p hg
    simpa only [d2263, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20060 (p : Pattern) (guard : d5849 p = 1) : d2234 p ≤ (0 : Int) + d3686 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d2234, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2234, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20061 (p : Pattern) (guard : d5849 p = 1) : d2264 p ≤ (0 : Int) + d3687 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20059 p hg
    simpa only [d2264, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20060 p hg
    simpa only [d2264, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20062 (p : Pattern) (guard : d5849 p = 1) : d2239 p ≤ (0 : Int) + d3688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d2239, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2239, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20063 (p : Pattern) (guard : d5849 p = 1) : d2242 p ≤ (0 : Int) + d3689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20062 p hg
    simpa only [d2242, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2242, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20064 (p : Pattern) (guard : d5849 p = 1) : d2265 p ≤ (0 : Int) + d3690 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20061 p hg
    simpa only [d2265, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20063 p hg
    simpa only [d2265, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20065 (p : Pattern) (guard : d5849 p = 1) : d2266 p ≤ (0 : Int) + d3691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2266, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20054 p hg
    simpa only [d2266, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2266, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2266, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20066 (p : Pattern) (guard : d5849 p = 1) : d2267 p ≤ (0 : Int) + d3692 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2267, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20065 p hg
    simpa only [d2267, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2267, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2267, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20067 (p : Pattern) (guard : d5849 p = 1) : d2268 p ≤ (0 : Int) + d3693 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2268, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20066 p hg
    simpa only [d2268, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2268, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2268, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20068 (p : Pattern) (guard : d5849 p = 1) : d2269 p ≤ (0 : Int) + d3694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2269, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20064 p hg
    simpa only [d2269, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2269, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20067 p hg
    simpa only [d2269, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20069 (p : Pattern) (guard : d5849 p = 1) : d2270 p ≤ (0 : Int) + d3695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2270, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20058 p hg
    simpa only [d2270, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2270, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20068 p hg
    simpa only [d2270, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20070 (p : Pattern) (guard : d5849 p = 1) : d2271 p ≤ (0 : Int) + d3696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2271, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20026 p hg
    simpa only [d2271, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2271, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2271, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20071 (p : Pattern) (guard : d5849 p = 1) : d2194 p ≤ (0 : Int) + d3658 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2194, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19856 p hg
    simpa only [d2194, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2194, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20028 p hg
    simpa only [d2194, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20072 (p : Pattern) (guard : d5849 p = 1) : d2195 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2195, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20071 p hg
    simpa only [d2195, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2195, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20030 p hg
    simpa only [d2195, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20073 (p : Pattern) (guard : d5849 p = 1) : d2272 p ≤ (0 : Int) + d3666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2272, d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20072 p hg
    simpa only [d2272, d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2272, d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20035 p hg
    simpa only [d2272, d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20074 (p : Pattern) (guard : d5849 p = 1) : d2273 p ≤ (0 : Int) + d3672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20073 p hg
    simpa only [d2273, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20041 p hg
    simpa only [d2273, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20075 (p : Pattern) (guard : d5849 p = 1) : d2274 p ≤ (0 : Int) + d3677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20074 p hg
    simpa only [d2274, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20046 p hg
    simpa only [d2274, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20076 (p : Pattern) (guard : d5849 p = 1) : d2275 p ≤ (0 : Int) + d3684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2275, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20075 p hg
    simpa only [d2275, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2275, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20057 p hg
    simpa only [d2275, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20077 (p : Pattern) (guard : d5849 p = 1) : d2276 p ≤ (0 : Int) + d3695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2276, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20076 p hg
    simpa only [d2276, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2276, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20068 p hg
    simpa only [d2276, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20078 (p : Pattern) (guard : d5849 p = 1) : d2277 p ≤ (0 : Int) + d3697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2277, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2277, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2277, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2277, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20079 (p : Pattern) (guard : d5849 p = 1) : d2278 p ≤ (0 : Int) + d3698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2278, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20078 p hg
    simpa only [d2278, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2278, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2278, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20080 (p : Pattern) (guard : d5849 p = 1) : d2279 p ≤ (0 : Int) + d3699 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2279, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2279, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2279, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2279, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20081 (p : Pattern) (guard : d5849 p = 1) : d2280 p ≤ (0 : Int) + d3700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2280, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20079 p hg
    simpa only [d2280, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2280, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20080 p hg
    simpa only [d2280, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20082 (p : Pattern) (guard : d5849 p = 1) : d2281 p ≤ (0 : Int) + d3701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2281, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20080 p hg
    simpa only [d2281, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2281, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2281, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20083 (p : Pattern) (guard : d5849 p = 1) : d2282 p ≤ (0 : Int) + d3702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2282, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20081 p hg
    simpa only [d2282, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2282, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20082 p hg
    simpa only [d2282, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20084 (p : Pattern) (guard : d5849 p = 1) : d2283 p ≤ (0 : Int) + d3703 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2283, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20082 p hg
    simpa only [d2283, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2283, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2283, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20085 (p : Pattern) (guard : d5849 p = 1) : d2284 p ≤ (0 : Int) + d3704 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2284, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20083 p hg
    simpa only [d2284, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2284, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20084 p hg
    simpa only [d2284, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20086 (p : Pattern) (guard : d5849 p = 1) : d2285 p ≤ (0 : Int) + d3705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2285, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20077 p hg
    simpa only [d2285, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2285, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20085 p hg
    simpa only [d2285, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20087 (p : Pattern) (guard : d5849 p = 1) : d2286 p ≤ (0 : Int) + d3706 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2286, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20070 p hg
    simpa only [d2286, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2286, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20086 p hg
    simpa only [d2286, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20088 (p : Pattern) (guard : d5849 p = 1) : d2287 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19853 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19885 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20089 (p : Pattern) (guard : d5849 p = 1) : d2288 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2288, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20088 p hg
    simpa only [d2288, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2288, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19886 p hg
    simpa only [d2288, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20090 (p : Pattern) (guard : d5849 p = 1) : d2289 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2289, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20089 p hg
    simpa only [d2289, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2289, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19907 p hg
    simpa only [d2289, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20091 (p : Pattern) (guard : d5849 p = 1) : d2290 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2290, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20090 p hg
    simpa only [d2290, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2290, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d2290, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20092 (p : Pattern) (guard : d5849 p = 1) : d2263 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19885 p hg
    simpa only [d2263, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19986 p hg
    simpa only [d2263, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20093 (p : Pattern) (guard : d5849 p = 1) : d2264 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20092 p hg
    simpa only [d2264, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19988 p hg
    simpa only [d2264, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20094 (p : Pattern) (guard : d5849 p = 1) : d2265 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20093 p hg
    simpa only [d2265, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20012 p hg
    simpa only [d2265, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20095 (p : Pattern) (guard : d5849 p = 1) : d2291 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2291, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20094 p hg
    simpa only [d2291, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2291, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20024 p hg
    simpa only [d2291, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20096 (p : Pattern) (guard : d5849 p = 1) : d2292 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2292, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20091 p hg
    simpa only [d2292, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2292, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20095 p hg
    simpa only [d2292, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20097 (p : Pattern) (guard : d5849 p = 1) : d2293 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2293, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20096 p hg
    simpa only [d2293, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2293, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2293, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20098 (p : Pattern) (guard : d5849 p = 1) : d2294 p ≤ (0 : Int) + d3716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2294, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2294, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2294, d3716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2294, d3716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20099 (p : Pattern) (guard : d5849 p = 1) : d2295 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2295, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20097 p hg
    simpa only [d2295, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2295, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20098 p hg
    simpa only [d2295, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20100 (p : Pattern) (guard : d5849 p = 1) : d2296 p ≤ (0 : Int) + d3718 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2296, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20087 p hg
    simpa only [d2296, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2296, d3718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20099 p hg
    simpa only [d2296, d3718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20101 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20102 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d2051 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20101 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20103 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3719 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20102 p hg
    simpa only [d14, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d14, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20104 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20103 p hg
    simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19830 p hg
    simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20105 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20106 (p : Pattern) (guard : d5849 p = 1) : d2297 p ≤ (0 : Int) + d3721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2297, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20104 p hg
    simpa only [d5849, d2297, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2297, d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20105 p hg
    simpa only [d5849, d2297, d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20107 (p : Pattern) (guard : d5849 p = 1) : d2298 p ≤ (0 : Int) + d3722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2298, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20106 p hg
    simpa only [d2298, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2298, d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2298, d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20108 (p : Pattern) (guard : d5849 p = 1) : d2299 p ≤ (0 : Int) + d3723 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2299, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20107 p hg
    simpa only [d2299, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2299, d3723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2299, d3723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20109 (p : Pattern) (guard : d5849 p = 1) : d2300 p ≤ (0 : Int) + d3724 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2300, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20108 p hg
    simpa only [d2300, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2300, d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19858 p hg
    simpa only [d2300, d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20110 (p : Pattern) (guard : d5849 p = 1) : d2301 p ≤ (0 : Int) + d3725 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2301, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20109 p hg
    simpa only [d2301, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2301, d3725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19886 p hg
    simpa only [d2301, d3725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20111 (p : Pattern) (guard : d5849 p = 1) : d2302 p ≤ (0 : Int) + d3726 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2302, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20110 p hg
    simpa only [d2302, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2302, d3726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19907 p hg
    simpa only [d2302, d3726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20112 (p : Pattern) (guard : d5849 p = 1) : d2303 p ≤ (0 : Int) + d3727 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2303, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20111 p hg
    simpa only [d2303, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2303, d3727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d2303, d3727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20113 (p : Pattern) (guard : d5849 p = 1) : d2304 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2304, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19853 p hg
    simpa only [d2304, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2304, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19986 p hg
    simpa only [d2304, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20114 (p : Pattern) (guard : d5849 p = 1) : d2305 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2305, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20113 p hg
    simpa only [d2305, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2305, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19988 p hg
    simpa only [d2305, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20115 (p : Pattern) (guard : d5849 p = 1) : d2306 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2306, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20114 p hg
    simpa only [d2306, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2306, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20012 p hg
    simpa only [d2306, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20116 (p : Pattern) (guard : d5849 p = 1) : d2307 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2307, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20115 p hg
    simpa only [d2307, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2307, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20024 p hg
    simpa only [d2307, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20117 (p : Pattern) (guard : d5849 p = 1) : d2308 p ≤ (0 : Int) + d3728 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2308, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20112 p hg
    simpa only [d2308, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2308, d3728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20116 p hg
    simpa only [d2308, d3728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20118 (p : Pattern) (guard : d5849 p = 1) : d2309 p ≤ (0 : Int) + d3729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2309, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20117 p hg
    simpa only [d2309, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2309, d3729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2309, d3729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20119 (p : Pattern) (guard : d5849 p = 1) : d2310 p ≤ (0 : Int) + d3705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2310, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2310, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2310, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20085 p hg
    simpa only [d2310, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20120 (p : Pattern) (guard : d5849 p = 1) : d2311 p ≤ (0 : Int) + d3730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2311, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20118 p hg
    simpa only [d2311, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2311, d3730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20119 p hg
    simpa only [d2311, d3730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20121 (p : Pattern) (guard : d5849 p = 1) : d2272 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19858 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19885 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20122 (p : Pattern) (guard : d5849 p = 1) : d2273 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20121 p hg
    simpa only [d2273, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19886 p hg
    simpa only [d2273, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20123 (p : Pattern) (guard : d5849 p = 1) : d2274 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20122 p hg
    simpa only [d2274, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19907 p hg
    simpa only [d2274, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20124 (p : Pattern) (guard : d5849 p = 1) : d2312 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2312, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20123 p hg
    simpa only [d2312, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2312, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d2312, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20125 (p : Pattern) (guard : d5849 p = 1) : d2313 p ≤ (0 : Int) + d3714 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2313, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20124 p hg
    simpa only [d2313, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2313, d3714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20095 p hg
    simpa only [d2313, d3714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20126 (p : Pattern) (guard : d5849 p = 1) : d2314 p ≤ (0 : Int) + d3715 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2314, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20125 p hg
    simpa only [d2314, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2314, d3715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20069 p hg
    simpa only [d2314, d3715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20127 (p : Pattern) (guard : d5849 p = 1) : d2315 p ≤ (0 : Int) + d3717 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2315, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20126 p hg
    simpa only [d2315, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2315, d3717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20098 p hg
    simpa only [d2315, d3717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20128 (p : Pattern) (guard : d5849 p = 1) : d2316 p ≤ (0 : Int) + d3731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2316, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20120 p hg
    simpa only [d2316, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2316, d3731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20127 p hg
    simpa only [d2316, d3731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20129 (p : Pattern) (guard : d5849 p = 1) : d2317 p ≤ (0 : Int) + d3732 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2317, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20100 p hg
    simpa only [d2317, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2317, d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20128 p hg
    simpa only [d2317, d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20130 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20131 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d428 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20130 p hg
    simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20132 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d102 p := by
  omega
theorem compare20133 (p : Pattern) (guard : d5843 p = 1) : d103 p ≤ (0 : Int) + d3733 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d103, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20131 p hg
    simpa only [d103, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d103, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20132 p hg
    simpa only [d103, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20134 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20135 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20136 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14648 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20137 (p : Pattern) (guard : d5848 p = 1) : d103 p ≤ (0 : Int) + d3734 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20133 p hg
    simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20136 p hg
    simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20138 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20139 (p : Pattern) (guard : d5849 p = 1) : d2318 p ≤ (0 : Int) + d3735 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2318, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20137 p hg
    simpa only [d5849, d2318, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2318, d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20138 p hg
    simpa only [d5849, d2318, d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20140 (p : Pattern) (guard : d5843 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20132 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20141 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20142 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d3736 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d103, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20141 p hg
    simpa only [d5847, d103, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20143 (p : Pattern) (guard : d5848 p = 1) : d103 p ≤ (0 : Int) + d3737 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20142 p hg
    simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20144 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3736 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20145 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3738 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20143 p hg
    simpa only [d5849, d2319, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20144 p hg
    simpa only [d5849, d2319, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20146 (p : Pattern) (guard : d5849 p = 1) : d2320 p ≤ (0 : Int) + d3739 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2320, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20139 p hg
    simpa only [d2320, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2320, d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d2320, d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20147 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20148 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d3740 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20135 p hg
    simpa only [d5847, d103, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20147 p hg
    simpa only [d5847, d103, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20149 (p : Pattern) (guard : d5848 p = 1) : d103 p ≤ (0 : Int) + d3741 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20148 p hg
    simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20150 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3740 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20151 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3742 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20149 p hg
    simpa only [d5849, d2319, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20150 p hg
    simpa only [d5849, d2319, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20152 (p : Pattern) (guard : d5849 p = 1) : d2321 p ≤ (0 : Int) + d3743 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20151 p hg
    simpa only [d2321, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2321, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20153 (p : Pattern) (guard : d5849 p = 1) : d2322 p ≤ (0 : Int) + d3744 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2322, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20146 p hg
    simpa only [d2322, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2322, d3744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20152 p hg
    simpa only [d2322, d3744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20154 (p : Pattern) (guard : d5848 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20140 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20136 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20155 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20156 (p : Pattern) (guard : d5849 p = 1) : d2323 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20154 p hg
    simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20155 p hg
    simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20157 (p : Pattern) (guard : d5849 p = 1) : d2324 p ≤ (0 : Int) + d3745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2324, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20156 p hg
    simpa only [d2324, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2324, d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20145 p hg
    simpa only [d2324, d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20158 (p : Pattern) (guard : d5849 p = 1) : d2325 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2325, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20157 p hg
    simpa only [d2325, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2325, d3746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20152 p hg
    simpa only [d2325, d3746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20159 (p : Pattern) (guard : d5849 p = 1) : d2326 p ≤ (0 : Int) + d3747 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2326, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20153 p hg
    simpa only [d2326, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2326, d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20158 p hg
    simpa only [d2326, d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
