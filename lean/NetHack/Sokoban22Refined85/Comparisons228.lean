/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons227
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31920 (p : Pattern) (guard : d5849 p = 1) : d3874 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31518 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31919 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31921 (p : Pattern) (guard : d5849 p = 1) : d3875 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3875, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31522 p hg
    simpa only [d3875, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3875, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3875, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31922 (p : Pattern) (guard : d5849 p = 1) : d3876 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3876, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31920 p hg
    simpa only [d3876, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3876, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31921 p hg
    simpa only [d3876, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31923 (p : Pattern) (guard : d5849 p = 1) : d3877 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3877, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31650 p hg
    simpa only [d3877, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3877, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31922 p hg
    simpa only [d3877, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31924 (p : Pattern) (guard : d5849 p = 1) : d3878 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3878, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31917 p hg
    simpa only [d3878, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3878, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31923 p hg
    simpa only [d3878, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31925 (p : Pattern) (guard : d5849 p = 1) : d3879 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3879, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31923 p hg
    simpa only [d3879, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3879, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31664 p hg
    simpa only [d3879, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31926 (p : Pattern) (guard : d5849 p = 1) : d3880 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3880, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31924 p hg
    simpa only [d3880, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3880, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31925 p hg
    simpa only [d3880, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31927 (p : Pattern) (guard : d5849 p = 1) : d3881 p ≤ (0 : Int) + d2404 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3881, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d3881, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3881, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31569 p hg
    simpa only [d3881, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31928 (p : Pattern) (guard : d5849 p = 1) : d3882 p ≤ (0 : Int) + d2405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3882, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31667 p hg
    simpa only [d3882, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3882, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31927 p hg
    simpa only [d3882, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31929 (p : Pattern) (guard : d5849 p = 1) : d3883 p ≤ (0 : Int) + d2406 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3883, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d3883, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3883, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31575 p hg
    simpa only [d3883, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31930 (p : Pattern) (guard : d5849 p = 1) : d3884 p ≤ (0 : Int) + d2407 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3884, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31671 p hg
    simpa only [d3884, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3884, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3884, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31931 (p : Pattern) (guard : d5849 p = 1) : d3885 p ≤ (0 : Int) + d2408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3885, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31929 p hg
    simpa only [d3885, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3885, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31930 p hg
    simpa only [d3885, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31932 (p : Pattern) (guard : d5849 p = 1) : d3886 p ≤ (0 : Int) + d2409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3886, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31928 p hg
    simpa only [d3886, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3886, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31931 p hg
    simpa only [d3886, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31933 (p : Pattern) (guard : d5849 p = 1) : d3887 p ≤ (0 : Int) + d2410 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3887, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31634 p hg
    simpa only [d3887, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3887, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31930 p hg
    simpa only [d3887, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31934 (p : Pattern) (guard : d5849 p = 1) : d3888 p ≤ (0 : Int) + d2411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3888, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31933 p hg
    simpa only [d3888, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3888, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31641 p hg
    simpa only [d3888, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31935 (p : Pattern) (guard : d5849 p = 1) : d3889 p ≤ (0 : Int) + d2412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3889, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31932 p hg
    simpa only [d3889, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3889, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31934 p hg
    simpa only [d3889, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31936 (p : Pattern) (guard : d5849 p = 1) : d3890 p ≤ (0 : Int) + d2413 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3890, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31926 p hg
    simpa only [d3890, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3890, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31935 p hg
    simpa only [d3890, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31937 (p : Pattern) (guard : d0 p = 1) : d3891 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31938 (p : Pattern) (guard : d5849 p = 1) : d3892 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3892, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31560 p hg
    simpa only [d5849, d3892, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3892, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31937 p hg
    simpa only [d5849, d3892, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31939 (p : Pattern) (guard : d5849 p = 1) : d3893 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31600 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31938 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31940 (p : Pattern) (guard : d5849 p = 1) : d3894 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3894, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31604 p hg
    simpa only [d3894, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3894, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3894, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31941 (p : Pattern) (guard : d5849 p = 1) : d3895 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3895, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31939 p hg
    simpa only [d3895, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3895, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31940 p hg
    simpa only [d3895, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31942 (p : Pattern) (guard : d5849 p = 1) : d3896 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3896, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31650 p hg
    simpa only [d3896, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3896, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31941 p hg
    simpa only [d3896, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31943 (p : Pattern) (guard : d5849 p = 1) : d3897 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3897, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31922 p hg
    simpa only [d3897, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3897, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d3897, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31944 (p : Pattern) (guard : d5849 p = 1) : d3898 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3898, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31942 p hg
    simpa only [d3898, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3898, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31943 p hg
    simpa only [d3898, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31945 (p : Pattern) (guard : d5849 p = 1) : d3899 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3899, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31922 p hg
    simpa only [d3899, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3899, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3899, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31946 (p : Pattern) (guard : d5849 p = 1) : d3900 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3900, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31945 p hg
    simpa only [d3900, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3900, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3900, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31947 (p : Pattern) (guard : d5849 p = 1) : d3901 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3901, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31944 p hg
    simpa only [d3901, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3901, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31946 p hg
    simpa only [d3901, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31948 (p : Pattern) (guard : d5849 p = 1) : d3902 p ≤ (0 : Int) + d2414 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3902, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31927 p hg
    simpa only [d3902, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3902, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d3902, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31949 (p : Pattern) (guard : d5849 p = 1) : d3903 p ≤ (0 : Int) + d2415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3903, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31930 p hg
    simpa only [d3903, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3903, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31640 p hg
    simpa only [d3903, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31950 (p : Pattern) (guard : d5849 p = 1) : d3904 p ≤ (0 : Int) + d2416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3904, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31948 p hg
    simpa only [d3904, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3904, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31949 p hg
    simpa only [d3904, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31951 (p : Pattern) (guard : d5849 p = 1) : d3905 p ≤ (0 : Int) + d2417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3905, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31930 p hg
    simpa only [d3905, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3905, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3905, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31952 (p : Pattern) (guard : d5849 p = 1) : d3906 p ≤ (0 : Int) + d2418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3906, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31951 p hg
    simpa only [d3906, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3906, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3906, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31953 (p : Pattern) (guard : d5849 p = 1) : d3907 p ≤ (0 : Int) + d2419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3907, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31950 p hg
    simpa only [d3907, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3907, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31952 p hg
    simpa only [d3907, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31954 (p : Pattern) (guard : d5849 p = 1) : d3908 p ≤ (0 : Int) + d2420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3908, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31947 p hg
    simpa only [d3908, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3908, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31953 p hg
    simpa only [d3908, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31955 (p : Pattern) (guard : d5849 p = 1) : d3909 p ≤ (0 : Int) + d2421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3909, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31936 p hg
    simpa only [d3909, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3909, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31954 p hg
    simpa only [d3909, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31956 (p : Pattern) (guard : d5849 p = 1) : d3910 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31532 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31652 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31957 (p : Pattern) (guard : d5849 p = 1) : d3911 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3911, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31647 p hg
    simpa only [d3911, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3911, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3911, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31958 (p : Pattern) (guard : d5849 p = 1) : d3912 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3912, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31956 p hg
    simpa only [d3912, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3912, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31957 p hg
    simpa only [d3912, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31959 (p : Pattern) (guard : d5849 p = 1) : d3913 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31958 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31657 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31960 (p : Pattern) (guard : d5849 p = 1) : d3914 p ≤ (0 : Int) + d2422 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3914, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31959 p hg
    simpa only [d3914, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3914, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31673 p hg
    simpa only [d3914, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31961 (p : Pattern) (guard : d5849 p = 1) : d3915 p ≤ (0 : Int) + d2423 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3915, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31960 p hg
    simpa only [d3915, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3915, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31674 p hg
    simpa only [d3915, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31962 (p : Pattern) (guard : d5847 p = 1) : d190 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14752 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31963 (p : Pattern) (guard : d5848 p = 1) : d190 p ≤ (0 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31962 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31964 (p : Pattern) (guard : d5849 p = 1) : d190 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31963 p hg
    simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31965 (p : Pattern) (guard : d5847 p = 1) : d315 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23785 p hg
    simpa only [d5847, d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31966 (p : Pattern) (guard : d5848 p = 1) : d3916 p ≤ (0 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29683 p hg
    simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31965 p hg
    simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31967 (p : Pattern) (guard : d5849 p = 1) : d3917 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3917, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d5849, d3917, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3917, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17512 p hg
    simpa only [d5849, d3917, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31968 (p : Pattern) (guard : d5849 p = 1) : d3918 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31964 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31969 (p : Pattern) (guard : d5849 p = 1) : d3919 p ≤ (0 : Int) + d2425 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3919, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d3919, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3919, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3919, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31970 (p : Pattern) (guard : d5849 p = 1) : d3920 p ≤ (0 : Int) + d2426 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3920, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d3920, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3920, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d3920, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31971 (p : Pattern) (guard : d5849 p = 1) : d3921 p ≤ (0 : Int) + d2427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3921, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d3921, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3921, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d3921, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31972 (p : Pattern) (guard : d5849 p = 1) : d3922 p ≤ (0 : Int) + d2428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3922, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d3922, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3922, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3922, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31973 (p : Pattern) (guard : d5849 p = 1) : d3923 p ≤ (0 : Int) + d2429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3923, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d3923, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3923, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3923, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31974 (p : Pattern) (guard : d5849 p = 1) : d3924 p ≤ (0 : Int) + d2430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3924, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31961 p hg
    simpa only [d3924, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3924, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d3924, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31975 (p : Pattern) (guard : d0 p = 1) : d3926 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31976 (p : Pattern) (guard : d5849 p = 1) : d3927 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3927, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31560 p hg
    simpa only [d5849, d3927, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3927, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31975 p hg
    simpa only [d5849, d3927, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31977 (p : Pattern) (guard : d5849 p = 1) : d3928 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3928, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31976 p hg
    simpa only [d3928, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3928, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3928, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31978 (p : Pattern) (guard : d5849 p = 1) : d3929 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3929, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d3929, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3929, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31977 p hg
    simpa only [d3929, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31979 (p : Pattern) (guard : d5849 p = 1) : d3930 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31978 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31667 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31980 (p : Pattern) (guard : d5849 p = 1) : d3931 p ≤ (0 : Int) + d2431 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3931, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d3931, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3931, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d3931, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31981 (p : Pattern) (guard : d5849 p = 1) : d3932 p ≤ (0 : Int) + d2432 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3932, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31979 p hg
    simpa only [d3932, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3932, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31980 p hg
    simpa only [d3932, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31982 (p : Pattern) (guard : d5849 p = 1) : d3933 p ≤ (0 : Int) + d2433 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3933, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31981 p hg
    simpa only [d3933, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3933, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31684 p hg
    simpa only [d3933, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31983 (p : Pattern) (guard : d5849 p = 1) : d3934 p ≤ (0 : Int) + d2434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3934, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d3934, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3934, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3934, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31984 (p : Pattern) (guard : d5849 p = 1) : d3935 p ≤ (0 : Int) + d2435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3935, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31983 p hg
    simpa only [d3935, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3935, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3935, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31985 (p : Pattern) (guard : d5849 p = 1) : d3936 p ≤ (0 : Int) + d2436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3936, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d3936, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3936, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3936, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31986 (p : Pattern) (guard : d5849 p = 1) : d3937 p ≤ (0 : Int) + d2437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3937, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d3937, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3937, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31985 p hg
    simpa only [d3937, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31987 (p : Pattern) (guard : d5849 p = 1) : d3938 p ≤ (0 : Int) + d2438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3938, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d3938, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3938, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d3938, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31988 (p : Pattern) (guard : d5849 p = 1) : d3939 p ≤ (0 : Int) + d2439 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3939, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31955 p hg
    simpa only [d3939, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3939, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31987 p hg
    simpa only [d3939, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31989 (p : Pattern) (guard : d5849 p = 1) : d3940 p ≤ (0 : Int) + d2440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3940, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31987 p hg
    simpa only [d3940, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3940, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3940, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31990 (p : Pattern) (guard : d5849 p = 1) : d3941 p ≤ (0 : Int) + d2441 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3941, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d3941, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3941, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31989 p hg
    simpa only [d3941, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31991 (p : Pattern) (guard : d5849 p = 1) : d3942 p ≤ (0 : Int) + d2442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3942, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31735 p hg
    simpa only [d3942, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3942, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31990 p hg
    simpa only [d3942, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31992 (p : Pattern) (guard : d5849 p = 1) : d3943 p ≤ (0 : Int) + d2443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3943, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31718 p hg
    simpa only [d3943, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3943, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d3943, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31993 (p : Pattern) (guard : d5849 p = 1) : d3944 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3944, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31782 p hg
    simpa only [d3944, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3944, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3944, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31994 (p : Pattern) (guard : d5849 p = 1) : d3945 p ≤ (0 : Int) + d2445 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3945, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31840 p hg
    simpa only [d3945, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3945, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31993 p hg
    simpa only [d3945, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31995 (p : Pattern) (guard : d5849 p = 1) : d3946 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3946, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31993 p hg
    simpa only [d3946, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3946, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3946, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31996 (p : Pattern) (guard : d5849 p = 1) : d3947 p ≤ (0 : Int) + d2447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3947, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31994 p hg
    simpa only [d3947, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3947, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31995 p hg
    simpa only [d3947, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31997 (p : Pattern) (guard : d5849 p = 1) : d3948 p ≤ (0 : Int) + d2448 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3948, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d3948, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3948, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3948, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31998 (p : Pattern) (guard : d5849 p = 1) : d3949 p ≤ (0 : Int) + d2449 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3949, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31848 p hg
    simpa only [d3949, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3949, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31997 p hg
    simpa only [d3949, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31999 (p : Pattern) (guard : d5849 p = 1) : d3950 p ≤ (0 : Int) + d2450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3950, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31997 p hg
    simpa only [d3950, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3950, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3950, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32000 (p : Pattern) (guard : d5849 p = 1) : d3951 p ≤ (0 : Int) + d2451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3951, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d3951, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3951, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31999 p hg
    simpa only [d3951, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32001 (p : Pattern) (guard : d5849 p = 1) : d3952 p ≤ (0 : Int) + d2452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3952, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31996 p hg
    simpa only [d3952, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3952, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32000 p hg
    simpa only [d3952, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32002 (p : Pattern) (guard : d5849 p = 1) : d3953 p ≤ (0 : Int) + d2453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3953, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31821 p hg
    simpa only [d3953, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3953, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32001 p hg
    simpa only [d3953, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32003 (p : Pattern) (guard : d5849 p = 1) : d3954 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3954, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3954, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3954, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3954, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32004 (p : Pattern) (guard : d5849 p = 1) : d3955 p ≤ (0 : Int) + d2454 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3955, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31884 p hg
    simpa only [d3955, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3955, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32003 p hg
    simpa only [d3955, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32005 (p : Pattern) (guard : d5849 p = 1) : d3956 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3956, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32003 p hg
    simpa only [d3956, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3956, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3956, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32006 (p : Pattern) (guard : d5849 p = 1) : d3957 p ≤ (0 : Int) + d2455 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3957, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32004 p hg
    simpa only [d3957, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3957, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32005 p hg
    simpa only [d3957, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32007 (p : Pattern) (guard : d5849 p = 1) : d3958 p ≤ (0 : Int) + d2456 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3958, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32006 p hg
    simpa only [d3958, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3958, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31892 p hg
    simpa only [d3958, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32008 (p : Pattern) (guard : d5849 p = 1) : d3959 p ≤ (0 : Int) + d2457 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3959, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31883 p hg
    simpa only [d3959, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3959, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32007 p hg
    simpa only [d3959, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32009 (p : Pattern) (guard : d5849 p = 1) : d3960 p ≤ (0 : Int) + d2458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3960, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d3960, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3960, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32008 p hg
    simpa only [d3960, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32010 (p : Pattern) (guard : d5849 p = 1) : d3961 p ≤ (0 : Int) + d2459 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3961, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32008 p hg
    simpa only [d3961, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3961, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31899 p hg
    simpa only [d3961, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32011 (p : Pattern) (guard : d5849 p = 1) : d3962 p ≤ (0 : Int) + d2460 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3962, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32009 p hg
    simpa only [d3962, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3962, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32010 p hg
    simpa only [d3962, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32012 (p : Pattern) (guard : d5849 p = 1) : d3820 p ≤ (0 : Int) + d2324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3820, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31762 p hg
    simpa only [d3820, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3820, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31857 p hg
    simpa only [d3820, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32013 (p : Pattern) (guard : d5849 p = 1) : d3822 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3822, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32012 p hg
    simpa only [d3822, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3822, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31859 p hg
    simpa only [d3822, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32014 (p : Pattern) (guard : d5849 p = 1) : d3822 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32013 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31860 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32015 (p : Pattern) (guard : d5849 p = 1) : d3963 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31766 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31862 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32016 (p : Pattern) (guard : d5849 p = 1) : d3964 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3964, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31857 p hg
    simpa only [d3964, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3964, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3964, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32017 (p : Pattern) (guard : d5849 p = 1) : d3965 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3965, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d3965, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3965, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d3965, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32018 (p : Pattern) (guard : d5849 p = 1) : d3966 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3966, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32017 p hg
    simpa only [d3966, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3966, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3966, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32019 (p : Pattern) (guard : d5849 p = 1) : d3967 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3967, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32014 p hg
    simpa only [d3967, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3967, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d3967, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32020 (p : Pattern) (guard : d5849 p = 1) : d3968 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3968, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d3968, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3968, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3968, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32021 (p : Pattern) (guard : d5849 p = 1) : d3969 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3969, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32020 p hg
    simpa only [d3969, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3969, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31785 p hg
    simpa only [d3969, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32022 (p : Pattern) (guard : d5849 p = 1) : d3970 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3970, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32019 p hg
    simpa only [d3970, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3970, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32021 p hg
    simpa only [d3970, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32023 (p : Pattern) (guard : d5849 p = 1) : d3971 p ≤ (0 : Int) + d2461 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3971, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31846 p hg
    simpa only [d3971, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3971, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31805 p hg
    simpa only [d3971, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32024 (p : Pattern) (guard : d5849 p = 1) : d3972 p ≤ (0 : Int) + d2462 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3972, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d3972, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3972, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32023 p hg
    simpa only [d3972, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32025 (p : Pattern) (guard : d5849 p = 1) : d3973 p ≤ (0 : Int) + d2463 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3973, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32024 p hg
    simpa only [d3973, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3973, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31997 p hg
    simpa only [d3973, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32026 (p : Pattern) (guard : d5849 p = 1) : d3974 p ≤ (0 : Int) + d2464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3974, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31878 p hg
    simpa only [d3974, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3974, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3974, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32027 (p : Pattern) (guard : d5849 p = 1) : d3975 p ≤ (0 : Int) + d2465 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3975, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32026 p hg
    simpa only [d3975, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3975, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3975, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32028 (p : Pattern) (guard : d5849 p = 1) : d3976 p ≤ (0 : Int) + d2466 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3976, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32027 p hg
    simpa only [d3976, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3976, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3976, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32029 (p : Pattern) (guard : d5849 p = 1) : d3977 p ≤ (0 : Int) + d2467 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3977, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32025 p hg
    simpa only [d3977, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3977, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32028 p hg
    simpa only [d3977, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32030 (p : Pattern) (guard : d5849 p = 1) : d3978 p ≤ (0 : Int) + d2468 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3978, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32022 p hg
    simpa only [d3978, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3978, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32029 p hg
    simpa only [d3978, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32031 (p : Pattern) (guard : d0 p = 1) : d3979 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32032 (p : Pattern) (guard : d5849 p = 1) : d3980 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3980, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31796 p hg
    simpa only [d5849, d3980, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3980, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32031 p hg
    simpa only [d5849, d3980, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32033 (p : Pattern) (guard : d5849 p = 1) : d3981 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31828 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32032 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32034 (p : Pattern) (guard : d5849 p = 1) : d3982 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3982, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31832 p hg
    simpa only [d3982, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3982, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3982, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32035 (p : Pattern) (guard : d5849 p = 1) : d3983 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3983, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32033 p hg
    simpa only [d3983, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3983, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32034 p hg
    simpa only [d3983, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32036 (p : Pattern) (guard : d5849 p = 1) : d3984 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3984, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32017 p hg
    simpa only [d3984, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3984, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32035 p hg
    simpa only [d3984, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32037 (p : Pattern) (guard : d0 p = 1) : d3985 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32038 (p : Pattern) (guard : d5849 p = 1) : d3986 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3986, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31811 p hg
    simpa only [d5849, d3986, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3986, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32037 p hg
    simpa only [d5849, d3986, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32039 (p : Pattern) (guard : d5849 p = 1) : d3987 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31771 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32038 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32040 (p : Pattern) (guard : d5849 p = 1) : d3988 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3988, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31775 p hg
    simpa only [d3988, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3988, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3988, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32041 (p : Pattern) (guard : d5849 p = 1) : d3989 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3989, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32039 p hg
    simpa only [d3989, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3989, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32040 p hg
    simpa only [d3989, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32042 (p : Pattern) (guard : d5849 p = 1) : d3990 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3990, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32041 p hg
    simpa only [d3990, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3990, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3990, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32043 (p : Pattern) (guard : d5849 p = 1) : d3991 p ≤ (0 : Int) + d2454 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3991, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32036 p hg
    simpa only [d3991, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3991, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32042 p hg
    simpa only [d3991, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32044 (p : Pattern) (guard : d5849 p = 1) : d3992 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3992, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32038 p hg
    simpa only [d3992, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3992, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3992, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32045 (p : Pattern) (guard : d5849 p = 1) : d3993 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3993, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31814 p hg
    simpa only [d3993, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3993, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d3993, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32046 (p : Pattern) (guard : d5849 p = 1) : d3994 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3994, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d3994, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3994, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3994, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32047 (p : Pattern) (guard : d5849 p = 1) : d3995 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3995, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d3995, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3995, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3995, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32048 (p : Pattern) (guard : d5849 p = 1) : d3996 p ≤ (0 : Int) + d2455 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3996, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32043 p hg
    simpa only [d3996, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3996, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d3996, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32049 (p : Pattern) (guard : d5849 p = 1) : d3997 p ≤ (0 : Int) + d2469 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3997, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31814 p hg
    simpa only [d3997, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3997, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31805 p hg
    simpa only [d3997, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32050 (p : Pattern) (guard : d5849 p = 1) : d3998 p ≤ (0 : Int) + d2470 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3998, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d3998, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3998, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d3998, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32051 (p : Pattern) (guard : d5849 p = 1) : d3999 p ≤ (0 : Int) + d2471 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3999, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d3999, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3999, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32027 p hg
    simpa only [d3999, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32052 (p : Pattern) (guard : d5849 p = 1) : d4000 p ≤ (0 : Int) + d2472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4000, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31589 p hg
    simpa only [d4000, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4000, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d4000, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32053 (p : Pattern) (guard : d5849 p = 1) : d4001 p ≤ (0 : Int) + d2473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4001, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d4001, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4001, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32052 p hg
    simpa only [d4001, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32054 (p : Pattern) (guard : d5849 p = 1) : d4002 p ≤ (0 : Int) + d2474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4002, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d4002, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4002, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32053 p hg
    simpa only [d4002, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32055 (p : Pattern) (guard : d5849 p = 1) : d4003 p ≤ (0 : Int) + d2475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4003, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32030 p hg
    simpa only [d4003, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4003, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32054 p hg
    simpa only [d4003, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32056 (p : Pattern) (guard : d5849 p = 1) : d4004 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31867 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32057 (p : Pattern) (guard : d5849 p = 1) : d4005 p ≤ (0 : Int) + d2476 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4005, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d4005, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4005, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d4005, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32058 (p : Pattern) (guard : d5849 p = 1) : d4006 p ≤ (0 : Int) + d2477 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4006, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32056 p hg
    simpa only [d4006, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4006, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32057 p hg
    simpa only [d4006, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32059 (p : Pattern) (guard : d5849 p = 1) : d4007 p ≤ (0 : Int) + d2478 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4007, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32058 p hg
    simpa only [d4007, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4007, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31888 p hg
    simpa only [d4007, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
