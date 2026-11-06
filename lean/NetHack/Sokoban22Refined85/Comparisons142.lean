/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19880 (p : Pattern) (guard : d5849 p = 1) : d2199 p ≤ (0 : Int) + d3564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2199, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19858 p hg
    simpa only [d2199, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2199, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19879 p hg
    simpa only [d2199, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19881 (p : Pattern) (guard : d5849 p = 1) : d2200 p ≤ (0 : Int) + d3565 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2200, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19854 p hg
    simpa only [d2200, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2200, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19880 p hg
    simpa only [d2200, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19882 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19883 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19849 p hg
    simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19884 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19883 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19885 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19884 p hg
    simpa only [d2201, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2201, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19886 (p : Pattern) (guard : d5849 p = 1) : d2202 p ≤ (0 : Int) + d3564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19885 p hg
    simpa only [d2202, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19879 p hg
    simpa only [d2202, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19887 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19888 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19889 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare19890 (p : Pattern) (guard : d5843 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19891 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14549 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19892 (p : Pattern) (guard : d5848 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19891 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19893 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19894 (p : Pattern) (guard : d5849 p = 1) : d2203 p ≤ (0 : Int) + d23 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19892 p hg
    simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19895 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19896 (p : Pattern) (guard : d5848 p = 1) : d24 p ≤ (0 : Int) + d3566 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19895 p hg
    simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19897 (p : Pattern) (guard : d5849 p = 1) : d2203 p ≤ (0 : Int) + d3567 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2203, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19896 p hg
    simpa only [d5849, d2203, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2203, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5849, d2203, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19898 (p : Pattern) (guard : d5849 p = 1) : d2203 p ≤ (0 : Int) + d3568 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19894 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19897 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19899 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19900 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d3569 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19888 p hg
    simpa only [d5847, d24, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19899 p hg
    simpa only [d5847, d24, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19901 (p : Pattern) (guard : d5848 p = 1) : d24 p ≤ (0 : Int) + d3570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19900 p hg
    simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19902 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3569 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19903 (p : Pattern) (guard : d5849 p = 1) : d2203 p ≤ (0 : Int) + d3571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2203, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19901 p hg
    simpa only [d5849, d2203, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2203, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19902 p hg
    simpa only [d5849, d2203, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19904 (p : Pattern) (guard : d5849 p = 1) : d2204 p ≤ (0 : Int) + d3572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2204, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19903 p hg
    simpa only [d2204, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2204, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2204, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19905 (p : Pattern) (guard : d5849 p = 1) : d2205 p ≤ (0 : Int) + d3573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2205, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19898 p hg
    simpa only [d2205, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2205, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19904 p hg
    simpa only [d2205, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19906 (p : Pattern) (guard : d5849 p = 1) : d2206 p ≤ (0 : Int) + d3574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2206, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19905 p hg
    simpa only [d2206, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2206, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2206, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19907 (p : Pattern) (guard : d5849 p = 1) : d2207 p ≤ (0 : Int) + d3575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19886 p hg
    simpa only [d2207, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19906 p hg
    simpa only [d2207, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19908 (p : Pattern) (guard : d5849 p = 1) : d2208 p ≤ (0 : Int) + d3576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2208, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19881 p hg
    simpa only [d2208, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2208, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19907 p hg
    simpa only [d2208, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19909 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19910 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d3577 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d14, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19909 p hg
    simpa only [d5847, d14, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19911 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3578 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19910 p hg
    simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19912 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19913 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3581 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19911 p hg
    simpa only [d5849, d2185, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19912 p hg
    simpa only [d5849, d2185, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19914 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3582 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19883 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19913 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19915 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19916 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19917 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d30 p := by
  omega
theorem compare19918 (p : Pattern) (guard : d5843 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19917 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19919 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19920 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d3583 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d31, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19919 p hg
    simpa only [d5847, d31, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19921 (p : Pattern) (guard : d5848 p = 1) : d31 p ≤ (0 : Int) + d3584 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19920 p hg
    simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19922 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19923 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3587 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19921 p hg
    simpa only [d5849, d2209, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19922 p hg
    simpa only [d5849, d2209, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19924 (p : Pattern) (guard : d5849 p = 1) : d2210 p ≤ (0 : Int) + d3588 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19923 p hg
    simpa only [d2210, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2210, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19925 (p : Pattern) (guard : d5849 p = 1) : d2211 p ≤ (0 : Int) + d3589 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2211, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2211, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2211, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19924 p hg
    simpa only [d2211, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19926 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19927 (p : Pattern) (guard : d5843 p = 1) : d6 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19928 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (0 : Int) + d34 p := by
  omega
theorem compare19929 (p : Pattern) (guard : d5843 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19930 (p : Pattern) (guard : d5847 p = 1) : d35 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19927 p hg
    simpa only [d5847, d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d35, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19931 (p : Pattern) (guard : d5848 p = 1) : d35 p ≤ (0 : Int) + d3590 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19930 p hg
    simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19932 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3592 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19933 (p : Pattern) (guard : d5849 p = 1) : d2212 p ≤ (0 : Int) + d3593 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2212, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19931 p hg
    simpa only [d5849, d2212, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2212, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19932 p hg
    simpa only [d5849, d2212, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19934 (p : Pattern) (guard : d5849 p = 1) : d2213 p ≤ (0 : Int) + d3594 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2213, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19933 p hg
    simpa only [d2213, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2213, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2213, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19935 (p : Pattern) (guard : d5849 p = 1) : d2214 p ≤ (0 : Int) + d3595 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2214, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2214, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2214, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19934 p hg
    simpa only [d2214, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19936 (p : Pattern) (guard : d5849 p = 1) : d2215 p ≤ (0 : Int) + d3596 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2215, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19925 p hg
    simpa only [d2215, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2215, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19935 p hg
    simpa only [d2215, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19937 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19938 (p : Pattern) (guard : d5843 p = 1) : d11 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19939 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  omega
theorem compare19940 (p : Pattern) (guard : d5843 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19941 (p : Pattern) (guard : d5847 p = 1) : d40 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d5847, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19942 (p : Pattern) (guard : d5848 p = 1) : d40 p ≤ (0 : Int) + d3597 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19941 p hg
    simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19943 (p : Pattern) (guard : d5849 p = 1) : d2216 p ≤ (0 : Int) + d3598 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2216, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19942 p hg
    simpa only [d5849, d2216, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2216, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5849, d2216, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19944 (p : Pattern) (guard : d5849 p = 1) : d2217 p ≤ (0 : Int) + d3599 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2217, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19943 p hg
    simpa only [d2217, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2217, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2217, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19945 (p : Pattern) (guard : d5849 p = 1) : d2218 p ≤ (0 : Int) + d3600 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2218, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2218, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2218, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19944 p hg
    simpa only [d2218, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19946 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19947 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d3601 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d18, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d3601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19946 p hg
    simpa only [d5847, d18, d3601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19948 (p : Pattern) (guard : d5848 p = 1) : d18 p ≤ (0 : Int) + d3602 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19947 p hg
    simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19949 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3603 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19950 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3604 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19948 p hg
    simpa only [d5849, d2196, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19949 p hg
    simpa only [d5849, d2196, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19951 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3605 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19866 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19950 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19952 (p : Pattern) (guard : d5849 p = 1) : d2219 p ≤ (0 : Int) + d3606 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2219, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19951 p hg
    simpa only [d2219, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2219, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2219, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19953 (p : Pattern) (guard : d5849 p = 1) : d2220 p ≤ (0 : Int) + d3607 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2220, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19945 p hg
    simpa only [d2220, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2220, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d2220, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19954 (p : Pattern) (guard : d5849 p = 1) : d2221 p ≤ (0 : Int) + d3608 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2221, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19936 p hg
    simpa only [d2221, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2221, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19953 p hg
    simpa only [d2221, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19955 (p : Pattern) (guard : d5849 p = 1) : d2222 p ≤ (0 : Int) + d3609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2222, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19914 p hg
    simpa only [d2222, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2222, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2222, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19956 (p : Pattern) (guard : d5849 p = 1) : d2223 p ≤ (0 : Int) + d3610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2223, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19955 p hg
    simpa only [d2223, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2223, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d2223, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19957 (p : Pattern) (guard : d5849 p = 1) : d2224 p ≤ (0 : Int) + d3611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2224, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19898 p hg
    simpa only [d2224, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2224, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2224, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19958 (p : Pattern) (guard : d5849 p = 1) : d2225 p ≤ (0 : Int) + d3612 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2225, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19957 p hg
    simpa only [d2225, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2225, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2225, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19959 (p : Pattern) (guard : d5849 p = 1) : d2226 p ≤ (0 : Int) + d3613 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2226, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19956 p hg
    simpa only [d2226, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2226, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19958 p hg
    simpa only [d2226, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19960 (p : Pattern) (guard : d5849 p = 1) : d2227 p ≤ (0 : Int) + d3614 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2227, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19954 p hg
    simpa only [d2227, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2227, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19959 p hg
    simpa only [d2227, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19961 (p : Pattern) (guard : d5849 p = 1) : d2228 p ≤ (0 : Int) + d3615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2228, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19908 p hg
    simpa only [d2228, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2228, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19960 p hg
    simpa only [d2228, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19962 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19963 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d1785 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19962 p hg
    simpa only [d5843, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19964 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19963 p hg
    simpa only [d14, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, d3616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d14, d3616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19965 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19964 p hg
    simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19830 p hg
    simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19966 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19967 (p : Pattern) (guard : d5849 p = 1) : d2229 p ≤ (0 : Int) + d3618 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2229, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19965 p hg
    simpa only [d5849, d2229, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2229, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19966 p hg
    simpa only [d5849, d2229, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19968 (p : Pattern) (guard : d5849 p = 1) : d2230 p ≤ (0 : Int) + d3619 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2230, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19967 p hg
    simpa only [d2230, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2230, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2230, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19969 (p : Pattern) (guard : d5849 p = 1) : d2231 p ≤ (0 : Int) + d3620 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2231, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19968 p hg
    simpa only [d2231, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2231, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2231, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19970 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14560 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19971 (p : Pattern) (guard : d5848 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19970 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19972 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19973 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d30 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19971 p hg
    simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19974 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19975 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d3585 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d31, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19974 p hg
    simpa only [d5847, d31, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19976 (p : Pattern) (guard : d5848 p = 1) : d31 p ≤ (0 : Int) + d3621 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19975 p hg
    simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19977 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3585 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19978 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3622 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19976 p hg
    simpa only [d5849, d2209, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19977 p hg
    simpa only [d5849, d2209, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19979 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3623 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19973 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19978 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19980 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19981 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d3624 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19916 p hg
    simpa only [d5847, d31, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19980 p hg
    simpa only [d5847, d31, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19982 (p : Pattern) (guard : d5848 p = 1) : d31 p ≤ (0 : Int) + d3625 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19981 p hg
    simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19983 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3624 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19984 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3626 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19982 p hg
    simpa only [d5849, d2209, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19983 p hg
    simpa only [d5849, d2209, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19985 (p : Pattern) (guard : d5849 p = 1) : d2210 p ≤ (0 : Int) + d3627 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19984 p hg
    simpa only [d2210, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2210, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19986 (p : Pattern) (guard : d5849 p = 1) : d2232 p ≤ (0 : Int) + d3628 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19979 p hg
    simpa only [d2232, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19985 p hg
    simpa only [d2232, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19987 (p : Pattern) (guard : d5849 p = 1) : d2233 p ≤ (0 : Int) + d3629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2233, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19969 p hg
    simpa only [d2233, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2233, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19986 p hg
    simpa only [d2233, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19988 (p : Pattern) (guard : d5849 p = 1) : d2234 p ≤ (0 : Int) + d3630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19879 p hg
    simpa only [d2234, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19905 p hg
    simpa only [d2234, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19989 (p : Pattern) (guard : d5849 p = 1) : d2235 p ≤ (0 : Int) + d3631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2235, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19987 p hg
    simpa only [d2235, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2235, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19988 p hg
    simpa only [d2235, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19990 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19991 (p : Pattern) (guard : d5843 p = 1) : d10 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19992 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare19993 (p : Pattern) (guard : d5843 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19994 (p : Pattern) (guard : d5847 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14599 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19995 (p : Pattern) (guard : d5848 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19994 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19996 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19997 (p : Pattern) (guard : d5849 p = 1) : d2236 p ≤ (0 : Int) + d57 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19995 p hg
    simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19998 (p : Pattern) (guard : d5847 p = 1) : d58 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19991 p hg
    simpa only [d5847, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19999 (p : Pattern) (guard : d5848 p = 1) : d58 p ≤ (0 : Int) + d3632 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19998 p hg
    simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20000 (p : Pattern) (guard : d5849 p = 1) : d2236 p ≤ (0 : Int) + d3633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2236, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19999 p hg
    simpa only [d5849, d2236, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2236, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5849, d2236, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20001 (p : Pattern) (guard : d5849 p = 1) : d2236 p ≤ (0 : Int) + d3634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19997 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20000 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20002 (p : Pattern) (guard : d5849 p = 1) : d2237 p ≤ (0 : Int) + d3635 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2237, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20000 p hg
    simpa only [d2237, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2237, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2237, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20003 (p : Pattern) (guard : d5849 p = 1) : d2238 p ≤ (0 : Int) + d3636 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2238, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20001 p hg
    simpa only [d2238, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2238, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20002 p hg
    simpa only [d2238, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20004 (p : Pattern) (guard : d5849 p = 1) : d2239 p ≤ (0 : Int) + d3637 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19879 p hg
    simpa only [d2239, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2239, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20005 (p : Pattern) (guard : d5847 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19938 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14577 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20006 (p : Pattern) (guard : d5848 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20005 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20007 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20008 (p : Pattern) (guard : d5849 p = 1) : d2216 p ≤ (0 : Int) + d39 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20006 p hg
    simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20009 (p : Pattern) (guard : d5849 p = 1) : d2216 p ≤ (0 : Int) + d3638 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20008 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19943 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20010 (p : Pattern) (guard : d5849 p = 1) : d2240 p ≤ (0 : Int) + d3639 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2240, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20009 p hg
    simpa only [d2240, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2240, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19944 p hg
    simpa only [d2240, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20011 (p : Pattern) (guard : d5849 p = 1) : d2241 p ≤ (0 : Int) + d3640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2241, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2241, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2241, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2241, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20012 (p : Pattern) (guard : d5849 p = 1) : d2242 p ≤ (0 : Int) + d3641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20004 p hg
    simpa only [d2242, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2242, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20013 (p : Pattern) (guard : d5849 p = 1) : d2243 p ≤ (0 : Int) + d3642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2243, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19989 p hg
    simpa only [d2243, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2243, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20012 p hg
    simpa only [d2243, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20014 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3643 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19973 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19923 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20015 (p : Pattern) (guard : d5849 p = 1) : d2244 p ≤ (0 : Int) + d3644 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2244, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d2244, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2244, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2244, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20016 (p : Pattern) (guard : d5849 p = 1) : d2245 p ≤ (0 : Int) + d3645 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2245, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19935 p hg
    simpa only [d2245, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2245, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20015 p hg
    simpa only [d2245, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20017 (p : Pattern) (guard : d5849 p = 1) : d2246 p ≤ (0 : Int) + d3646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2246, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d2246, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2246, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19957 p hg
    simpa only [d2246, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20018 (p : Pattern) (guard : d5849 p = 1) : d2247 p ≤ (0 : Int) + d3647 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2247, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20016 p hg
    simpa only [d2247, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2247, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20017 p hg
    simpa only [d2247, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20019 (p : Pattern) (guard : d5849 p = 1) : d2248 p ≤ (0 : Int) + d3648 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2248, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20001 p hg
    simpa only [d2248, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2248, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2248, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
