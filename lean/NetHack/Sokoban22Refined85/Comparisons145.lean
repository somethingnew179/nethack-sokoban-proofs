/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20300 (p : Pattern) (guard : d5849 p = 1) : d2378 p ≤ (0 : Int) + d3846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2378, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20298 p hg
    simpa only [d2378, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2378, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20299 p hg
    simpa only [d2378, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20301 (p : Pattern) (guard : d5849 p = 1) : d2358 p ≤ (0 : Int) + d3847 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2358, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2358, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2358, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2358, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20302 (p : Pattern) (guard : d5849 p = 1) : d2359 p ≤ (0 : Int) + d3848 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2359, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20301 p hg
    simpa only [d2359, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2359, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2359, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20303 (p : Pattern) (guard : d5849 p = 1) : d2379 p ≤ (0 : Int) + d3849 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2379, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20300 p hg
    simpa only [d2379, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2379, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20302 p hg
    simpa only [d2379, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20304 (p : Pattern) (guard : d5849 p = 1) : d2380 p ≤ (0 : Int) + d3850 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2380, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20293 p hg
    simpa only [d2380, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2380, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2380, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20305 (p : Pattern) (guard : d5849 p = 1) : d2381 p ≤ (0 : Int) + d3851 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2381, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20304 p hg
    simpa only [d2381, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2381, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2381, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20306 (p : Pattern) (guard : d5849 p = 1) : d2382 p ≤ (0 : Int) + d3852 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2382, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20305 p hg
    simpa only [d2382, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2382, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2382, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20307 (p : Pattern) (guard : d5849 p = 1) : d2383 p ≤ (0 : Int) + d3853 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2383, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20303 p hg
    simpa only [d2383, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2383, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20306 p hg
    simpa only [d2383, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20308 (p : Pattern) (guard : d5849 p = 1) : d2384 p ≤ (0 : Int) + d3854 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2384, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20297 p hg
    simpa only [d2384, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2384, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20307 p hg
    simpa only [d2384, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20309 (p : Pattern) (guard : d5849 p = 1) : d2385 p ≤ (0 : Int) + d3855 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2385, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20268 p hg
    simpa only [d2385, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2385, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20308 p hg
    simpa only [d2385, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20310 (p : Pattern) (guard : d5849 p = 1) : d2386 p ≤ (0 : Int) + d3856 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2386, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20187 p hg
    simpa only [d2386, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2386, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2386, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20311 (p : Pattern) (guard : d5849 p = 1) : d2387 p ≤ (0 : Int) + d3857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2387, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20310 p hg
    simpa only [d2387, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2387, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2387, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20312 (p : Pattern) (guard : d5849 p = 1) : d2388 p ≤ (0 : Int) + d3858 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2388, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20311 p hg
    simpa only [d2388, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2388, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2388, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20313 (p : Pattern) (guard : d5849 p = 1) : d2389 p ≤ (0 : Int) + d3859 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2389, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20312 p hg
    simpa only [d2389, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2389, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2389, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20314 (p : Pattern) (guard : d5849 p = 1) : d2390 p ≤ (0 : Int) + d3860 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2390, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20308 p hg
    simpa only [d2390, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2390, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20313 p hg
    simpa only [d2390, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20315 (p : Pattern) (guard : d5849 p = 1) : d2391 p ≤ (0 : Int) + d3861 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2391, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20309 p hg
    simpa only [d2391, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2391, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20314 p hg
    simpa only [d2391, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20316 (p : Pattern) (guard : d5849 p = 1) : d2392 p ≤ (0 : Int) + d3746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20158 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20163 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20317 (p : Pattern) (guard : d5849 p = 1) : d2393 p ≤ (0 : Int) + d3862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2393, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20316 p hg
    simpa only [d2393, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2393, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20185 p hg
    simpa only [d2393, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20318 (p : Pattern) (guard : d5849 p = 1) : d2394 p ≤ (0 : Int) + d3863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2394, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20317 p hg
    simpa only [d2394, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2394, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20188 p hg
    simpa only [d2394, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20319 (p : Pattern) (guard : d5849 p = 1) : d2395 p ≤ (0 : Int) + d3864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2395, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20318 p hg
    simpa only [d2395, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2395, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20230 p hg
    simpa only [d2395, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20320 (p : Pattern) (guard : d5849 p = 1) : d2377 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20163 p hg
    simpa only [d2377, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20252 p hg
    simpa only [d2377, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20321 (p : Pattern) (guard : d5849 p = 1) : d2378 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2378, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20320 p hg
    simpa only [d2378, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2378, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20254 p hg
    simpa only [d2378, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20322 (p : Pattern) (guard : d5849 p = 1) : d2379 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2379, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20321 p hg
    simpa only [d2379, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2379, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20257 p hg
    simpa only [d2379, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20323 (p : Pattern) (guard : d5849 p = 1) : d2396 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2396, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20322 p hg
    simpa only [d2396, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2396, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20266 p hg
    simpa only [d2396, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20324 (p : Pattern) (guard : d5849 p = 1) : d2397 p ≤ (0 : Int) + d3865 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2397, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20319 p hg
    simpa only [d2397, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2397, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20323 p hg
    simpa only [d2397, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20325 (p : Pattern) (guard : d5849 p = 1) : d2398 p ≤ (0 : Int) + d3866 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2398, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20324 p hg
    simpa only [d2398, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2398, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20308 p hg
    simpa only [d2398, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20326 (p : Pattern) (guard : d5849 p = 1) : d2399 p ≤ (0 : Int) + d3867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2399, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20308 p hg
    simpa only [d2399, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2399, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2399, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20327 (p : Pattern) (guard : d5849 p = 1) : d2400 p ≤ (0 : Int) + d3868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2400, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20325 p hg
    simpa only [d2400, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2400, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20326 p hg
    simpa only [d2400, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20328 (p : Pattern) (guard : d5849 p = 1) : d2401 p ≤ (0 : Int) + d3869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2401, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20315 p hg
    simpa only [d2401, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2401, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20327 p hg
    simpa only [d2401, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20329 (p : Pattern) (guard : d5849 p = 1) : d2402 p ≤ (0 : Int) + d3870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2402, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20100 p hg
    simpa only [d2402, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2402, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20328 p hg
    simpa only [d2402, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20330 (p : Pattern) (guard : d5849 p = 1) : d2403 p ≤ (0 : Int) + d3871 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2403, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20129 p hg
    simpa only [d2403, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2403, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20329 p hg
    simpa only [d2403, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20331 (p : Pattern) (guard : d5849 p = 1) : d2272 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20072 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20031 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20332 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3872 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20333 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3873 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19948 p hg
    simpa only [d5849, d2196, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20332 p hg
    simpa only [d5849, d2196, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20334 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3874 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19866 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20333 p hg
    simpa only [d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20335 (p : Pattern) (guard : d5849 p = 1) : d2197 p ≤ (0 : Int) + d3875 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19871 p hg
    simpa only [d2197, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2197, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20336 (p : Pattern) (guard : d5849 p = 1) : d2198 p ≤ (0 : Int) + d3876 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20334 p hg
    simpa only [d2198, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20335 p hg
    simpa only [d2198, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20337 (p : Pattern) (guard : d5849 p = 1) : d2202 p ≤ (0 : Int) + d3877 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20031 p hg
    simpa only [d2202, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2202, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20336 p hg
    simpa only [d2202, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20338 (p : Pattern) (guard : d5849 p = 1) : d2273 p ≤ (0 : Int) + d3878 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20331 p hg
    simpa only [d2273, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2273, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20337 p hg
    simpa only [d2273, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20339 (p : Pattern) (guard : d5849 p = 1) : d2207 p ≤ (0 : Int) + d3879 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20337 p hg
    simpa only [d2207, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2207, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20045 p hg
    simpa only [d2207, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20340 (p : Pattern) (guard : d5849 p = 1) : d2274 p ≤ (0 : Int) + d3880 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20338 p hg
    simpa only [d2274, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2274, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20339 p hg
    simpa only [d2274, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20341 (p : Pattern) (guard : d5849 p = 1) : d2404 p ≤ (0 : Int) + d3881 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2404, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d2404, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2404, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19934 p hg
    simpa only [d2404, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20342 (p : Pattern) (guard : d5849 p = 1) : d2405 p ≤ (0 : Int) + d3882 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2405, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20048 p hg
    simpa only [d2405, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2405, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20341 p hg
    simpa only [d2405, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20343 (p : Pattern) (guard : d5849 p = 1) : d2406 p ≤ (0 : Int) + d3883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2406, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d2406, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2406, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19944 p hg
    simpa only [d2406, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20344 (p : Pattern) (guard : d5849 p = 1) : d2407 p ≤ (0 : Int) + d3884 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2407, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20053 p hg
    simpa only [d2407, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2407, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2407, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20345 (p : Pattern) (guard : d5849 p = 1) : d2408 p ≤ (0 : Int) + d3885 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2408, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20343 p hg
    simpa only [d2408, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2408, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20344 p hg
    simpa only [d2408, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20346 (p : Pattern) (guard : d5849 p = 1) : d2409 p ≤ (0 : Int) + d3886 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2409, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20342 p hg
    simpa only [d2409, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2409, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20345 p hg
    simpa only [d2409, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20347 (p : Pattern) (guard : d5849 p = 1) : d2410 p ≤ (0 : Int) + d3887 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2410, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20015 p hg
    simpa only [d2410, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2410, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20344 p hg
    simpa only [d2410, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20348 (p : Pattern) (guard : d5849 p = 1) : d2411 p ≤ (0 : Int) + d3888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2411, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20347 p hg
    simpa only [d2411, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2411, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20022 p hg
    simpa only [d2411, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20349 (p : Pattern) (guard : d5849 p = 1) : d2412 p ≤ (0 : Int) + d3889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2412, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20346 p hg
    simpa only [d2412, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2412, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20348 p hg
    simpa only [d2412, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20350 (p : Pattern) (guard : d5849 p = 1) : d2413 p ≤ (0 : Int) + d3890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2413, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20340 p hg
    simpa only [d2413, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2413, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20349 p hg
    simpa only [d2413, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20351 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3891 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20352 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3892 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19921 p hg
    simpa only [d5849, d2209, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20351 p hg
    simpa only [d5849, d2209, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20353 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3893 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19973 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20352 p hg
    simpa only [d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20354 (p : Pattern) (guard : d5849 p = 1) : d2210 p ≤ (0 : Int) + d3894 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19978 p hg
    simpa only [d2210, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2210, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20355 (p : Pattern) (guard : d5849 p = 1) : d2232 p ≤ (0 : Int) + d3895 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20353 p hg
    simpa only [d2232, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20354 p hg
    simpa only [d2232, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20356 (p : Pattern) (guard : d5849 p = 1) : d2263 p ≤ (0 : Int) + d3896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20031 p hg
    simpa only [d2263, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2263, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20355 p hg
    simpa only [d2263, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20357 (p : Pattern) (guard : d5849 p = 1) : d2234 p ≤ (0 : Int) + d3897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20336 p hg
    simpa only [d2234, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2234, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2234, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20358 (p : Pattern) (guard : d5849 p = 1) : d2264 p ≤ (0 : Int) + d3898 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20356 p hg
    simpa only [d2264, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2264, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20357 p hg
    simpa only [d2264, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20359 (p : Pattern) (guard : d5849 p = 1) : d2239 p ≤ (0 : Int) + d3899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20336 p hg
    simpa only [d2239, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2239, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20003 p hg
    simpa only [d2239, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20360 (p : Pattern) (guard : d5849 p = 1) : d2242 p ≤ (0 : Int) + d3900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20359 p hg
    simpa only [d2242, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2242, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20011 p hg
    simpa only [d2242, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20361 (p : Pattern) (guard : d5849 p = 1) : d2265 p ≤ (0 : Int) + d3901 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20358 p hg
    simpa only [d2265, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2265, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20360 p hg
    simpa only [d2265, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20362 (p : Pattern) (guard : d5849 p = 1) : d2414 p ≤ (0 : Int) + d3902 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2414, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20341 p hg
    simpa only [d2414, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2414, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19952 p hg
    simpa only [d2414, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20363 (p : Pattern) (guard : d5849 p = 1) : d2415 p ≤ (0 : Int) + d3903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2415, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20344 p hg
    simpa only [d2415, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2415, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20021 p hg
    simpa only [d2415, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20364 (p : Pattern) (guard : d5849 p = 1) : d2416 p ≤ (0 : Int) + d3904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2416, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20362 p hg
    simpa only [d2416, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2416, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20363 p hg
    simpa only [d2416, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20365 (p : Pattern) (guard : d5849 p = 1) : d2417 p ≤ (0 : Int) + d3905 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2417, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20344 p hg
    simpa only [d2417, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2417, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2417, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20366 (p : Pattern) (guard : d5849 p = 1) : d2418 p ≤ (0 : Int) + d3906 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2418, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20365 p hg
    simpa only [d2418, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2418, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2418, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20367 (p : Pattern) (guard : d5849 p = 1) : d2419 p ≤ (0 : Int) + d3907 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2419, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20364 p hg
    simpa only [d2419, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2419, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20366 p hg
    simpa only [d2419, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20368 (p : Pattern) (guard : d5849 p = 1) : d2420 p ≤ (0 : Int) + d3908 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2420, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20361 p hg
    simpa only [d2420, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2420, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20367 p hg
    simpa only [d2420, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20369 (p : Pattern) (guard : d5849 p = 1) : d2421 p ≤ (0 : Int) + d3909 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2421, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20350 p hg
    simpa only [d2421, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2421, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20368 p hg
    simpa only [d2421, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20370 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3910 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19883 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20033 p hg
    simpa only [d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20371 (p : Pattern) (guard : d5849 p = 1) : d2187 p ≤ (0 : Int) + d3911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20028 p hg
    simpa only [d2187, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2187, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20372 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20370 p hg
    simpa only [d2201, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2201, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20371 p hg
    simpa only [d2201, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20373 (p : Pattern) (guard : d5849 p = 1) : d2201 p ≤ (0 : Int) + d3913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20372 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20038 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20374 (p : Pattern) (guard : d5849 p = 1) : d2422 p ≤ (0 : Int) + d3914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2422, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20373 p hg
    simpa only [d2422, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2422, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20055 p hg
    simpa only [d2422, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20375 (p : Pattern) (guard : d5849 p = 1) : d2423 p ≤ (0 : Int) + d3915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2423, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20374 p hg
    simpa only [d2423, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2423, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20056 p hg
    simpa only [d2423, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20376 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20377 (p : Pattern) (guard : d5843 p = 1) : d8 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20378 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (0 : Int) + d190 p := by
  omega
theorem compare20379 (p : Pattern) (guard : d5843 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20380 (p : Pattern) (guard : d5847 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14752 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20381 (p : Pattern) (guard : d5848 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20380 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20382 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20383 (p : Pattern) (guard : d5849 p = 1) : d2424 p ≤ (0 : Int) + d190 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20381 p hg
    simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5849, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20384 (p : Pattern) (guard : d5847 p = 1) : d191 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d5847, d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d191, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20385 (p : Pattern) (guard : d5848 p = 1) : d191 p ≤ (0 : Int) + d3916 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20384 p hg
    simpa only [d5848, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20386 (p : Pattern) (guard : d5849 p = 1) : d2424 p ≤ (0 : Int) + d3917 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2424, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20385 p hg
    simpa only [d5849, d2424, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2424, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5849, d2424, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20387 (p : Pattern) (guard : d5849 p = 1) : d2424 p ≤ (0 : Int) + d3918 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20383 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20388 (p : Pattern) (guard : d5849 p = 1) : d2425 p ≤ (0 : Int) + d3919 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2425, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d2425, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2425, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2425, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20389 (p : Pattern) (guard : d5849 p = 1) : d2426 p ≤ (0 : Int) + d3920 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2426, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d2426, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2426, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d2426, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20390 (p : Pattern) (guard : d5849 p = 1) : d2427 p ≤ (0 : Int) + d3921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2427, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d2427, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2427, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d2427, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20391 (p : Pattern) (guard : d5849 p = 1) : d2428 p ≤ (0 : Int) + d3922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2428, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d2428, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2428, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2428, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20392 (p : Pattern) (guard : d5849 p = 1) : d2429 p ≤ (0 : Int) + d3923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2429, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d2429, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2429, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2429, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20393 (p : Pattern) (guard : d5849 p = 1) : d2430 p ≤ (0 : Int) + d3924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2430, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20375 p hg
    simpa only [d2430, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2430, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d2430, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20394 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3926 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20395 (p : Pattern) (guard : d5849 p = 1) : d2209 p ≤ (0 : Int) + d3927 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19921 p hg
    simpa only [d5849, d2209, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20394 p hg
    simpa only [d5849, d2209, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20396 (p : Pattern) (guard : d5849 p = 1) : d2210 p ≤ (0 : Int) + d3928 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d2210, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2210, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2210, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20397 (p : Pattern) (guard : d5849 p = 1) : d2232 p ≤ (0 : Int) + d3929 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20014 p hg
    simpa only [d2232, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2232, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20396 p hg
    simpa only [d2232, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20398 (p : Pattern) (guard : d5849 p = 1) : d2232 p ≤ (0 : Int) + d3930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20048 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20399 (p : Pattern) (guard : d5849 p = 1) : d2431 p ≤ (0 : Int) + d3931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2431, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20040 p hg
    simpa only [d2431, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2431, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2431, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20400 (p : Pattern) (guard : d5849 p = 1) : d2432 p ≤ (0 : Int) + d3932 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2432, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20398 p hg
    simpa only [d2432, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2432, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20399 p hg
    simpa only [d2432, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20401 (p : Pattern) (guard : d5849 p = 1) : d2433 p ≤ (0 : Int) + d3933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2433, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d2433, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2433, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20066 p hg
    simpa only [d2433, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20402 (p : Pattern) (guard : d5849 p = 1) : d2434 p ≤ (0 : Int) + d3934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2434, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d2434, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2434, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2434, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20403 (p : Pattern) (guard : d5849 p = 1) : d2435 p ≤ (0 : Int) + d3935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2435, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d2435, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2435, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2435, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20404 (p : Pattern) (guard : d5849 p = 1) : d2436 p ≤ (0 : Int) + d3936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2436, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20403 p hg
    simpa only [d2436, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2436, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2436, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20405 (p : Pattern) (guard : d5849 p = 1) : d2437 p ≤ (0 : Int) + d3937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2437, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20401 p hg
    simpa only [d2437, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2437, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20404 p hg
    simpa only [d2437, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20406 (p : Pattern) (guard : d5849 p = 1) : d2438 p ≤ (0 : Int) + d3938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2438, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d2438, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2438, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20405 p hg
    simpa only [d2438, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20407 (p : Pattern) (guard : d5849 p = 1) : d2439 p ≤ (0 : Int) + d3939 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2439, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20369 p hg
    simpa only [d2439, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2439, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20406 p hg
    simpa only [d2439, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20408 (p : Pattern) (guard : d5849 p = 1) : d2440 p ≤ (0 : Int) + d3940 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2440, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20406 p hg
    simpa only [d2440, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2440, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2440, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20409 (p : Pattern) (guard : d5849 p = 1) : d2441 p ≤ (0 : Int) + d3941 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2441, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20407 p hg
    simpa only [d2441, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2441, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d2441, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20410 (p : Pattern) (guard : d5849 p = 1) : d2442 p ≤ (0 : Int) + d3942 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2442, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20120 p hg
    simpa only [d2442, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2442, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20409 p hg
    simpa only [d2442, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20411 (p : Pattern) (guard : d5849 p = 1) : d2443 p ≤ (0 : Int) + d3943 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2443, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20100 p hg
    simpa only [d2443, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2443, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20410 p hg
    simpa only [d2443, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20412 (p : Pattern) (guard : d5849 p = 1) : d2444 p ≤ (0 : Int) + d3944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20184 p hg
    simpa only [d2444, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2444, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20413 (p : Pattern) (guard : d5849 p = 1) : d2445 p ≤ (0 : Int) + d3945 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2445, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20253 p hg
    simpa only [d2445, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2445, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d2445, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20414 (p : Pattern) (guard : d5849 p = 1) : d2446 p ≤ (0 : Int) + d3946 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d2446, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2446, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20415 (p : Pattern) (guard : d5849 p = 1) : d2447 p ≤ (0 : Int) + d3947 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2447, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20413 p hg
    simpa only [d2447, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2447, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20414 p hg
    simpa only [d2447, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20416 (p : Pattern) (guard : d5849 p = 1) : d2448 p ≤ (0 : Int) + d3948 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2448, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d2448, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2448, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2448, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20417 (p : Pattern) (guard : d5849 p = 1) : d2449 p ≤ (0 : Int) + d3949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2449, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20261 p hg
    simpa only [d2449, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2449, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20416 p hg
    simpa only [d2449, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20418 (p : Pattern) (guard : d5849 p = 1) : d2450 p ≤ (0 : Int) + d3950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2450, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20416 p hg
    simpa only [d2450, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2450, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2450, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20419 (p : Pattern) (guard : d5849 p = 1) : d2451 p ≤ (0 : Int) + d3951 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2451, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20417 p hg
    simpa only [d2451, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2451, d3951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20418 p hg
    simpa only [d2451, d3951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20420 (p : Pattern) (guard : d5849 p = 1) : d2452 p ≤ (0 : Int) + d3952 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2452, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20415 p hg
    simpa only [d2452, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2452, d3952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20419 p hg
    simpa only [d2452, d3952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20421 (p : Pattern) (guard : d5849 p = 1) : d2453 p ≤ (0 : Int) + d3953 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2453, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20231 p hg
    simpa only [d2453, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2453, d3953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20420 p hg
    simpa only [d2453, d3953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20422 (p : Pattern) (guard : d5849 p = 1) : d2444 p ≤ (0 : Int) + d3954 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2444, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2444, d3954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20423 (p : Pattern) (guard : d5849 p = 1) : d2454 p ≤ (0 : Int) + d3955 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2454, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20298 p hg
    simpa only [d2454, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2454, d3955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20422 p hg
    simpa only [d2454, d3955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20424 (p : Pattern) (guard : d5849 p = 1) : d2446 p ≤ (0 : Int) + d3956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20422 p hg
    simpa only [d2446, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2446, d3956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20425 (p : Pattern) (guard : d5849 p = 1) : d2455 p ≤ (0 : Int) + d3957 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2455, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20423 p hg
    simpa only [d2455, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2455, d3957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20424 p hg
    simpa only [d2455, d3957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20426 (p : Pattern) (guard : d5849 p = 1) : d2456 p ≤ (0 : Int) + d3958 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2456, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d2456, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2456, d3958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20306 p hg
    simpa only [d2456, d3958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20427 (p : Pattern) (guard : d5849 p = 1) : d2457 p ≤ (0 : Int) + d3959 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2457, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20297 p hg
    simpa only [d2457, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2457, d3959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d2457, d3959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20428 (p : Pattern) (guard : d5849 p = 1) : d2458 p ≤ (0 : Int) + d3960 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2458, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20421 p hg
    simpa only [d2458, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2458, d3960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20427 p hg
    simpa only [d2458, d3960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20429 (p : Pattern) (guard : d5849 p = 1) : d2459 p ≤ (0 : Int) + d3961 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2459, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20427 p hg
    simpa only [d2459, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2459, d3961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20313 p hg
    simpa only [d2459, d3961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20430 (p : Pattern) (guard : d5849 p = 1) : d2460 p ≤ (0 : Int) + d3962 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2460, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d2460, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2460, d3962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20429 p hg
    simpa only [d2460, d3962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20431 (p : Pattern) (guard : d5849 p = 1) : d2324 p ≤ (0 : Int) + d3820 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2324, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20156 p hg
    simpa only [d2324, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2324, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20270 p hg
    simpa only [d2324, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20432 (p : Pattern) (guard : d5849 p = 1) : d2325 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2325, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20431 p hg
    simpa only [d2325, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2325, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20272 p hg
    simpa only [d2325, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20433 (p : Pattern) (guard : d5849 p = 1) : d2392 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20432 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20273 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20434 (p : Pattern) (guard : d5849 p = 1) : d2319 p ≤ (0 : Int) + d3963 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20161 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20275 p hg
    simpa only [d3963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20435 (p : Pattern) (guard : d5849 p = 1) : d2321 p ≤ (0 : Int) + d3964 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20270 p hg
    simpa only [d2321, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2321, d3964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2321, d3964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20436 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d3965 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20434 p hg
    simpa only [d2327, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2327, d3965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20435 p hg
    simpa only [d2327, d3965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20437 (p : Pattern) (guard : d5849 p = 1) : d2331 p ≤ (0 : Int) + d3966 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20436 p hg
    simpa only [d2331, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2331, d3966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20438 (p : Pattern) (guard : d5849 p = 1) : d2393 p ≤ (0 : Int) + d3967 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2393, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20433 p hg
    simpa only [d2393, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2393, d3967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20437 p hg
    simpa only [d2393, d3967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20439 (p : Pattern) (guard : d5849 p = 1) : d2331 p ≤ (0 : Int) + d3968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20277 p hg
    simpa only [d2331, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2331, d3968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2331, d3968, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
