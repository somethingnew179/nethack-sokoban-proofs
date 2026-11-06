/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20440 (p : Pattern) (guard : d5849 p = 1) : d2334 p ≤ (0 : Int) + d3969 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20439 p hg
    simpa only [d2334, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2334, d3969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20187 p hg
    simpa only [d2334, d3969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20441 (p : Pattern) (guard : d5849 p = 1) : d2394 p ≤ (0 : Int) + d3970 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2394, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20438 p hg
    simpa only [d2394, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2394, d3970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20440 p hg
    simpa only [d2394, d3970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20442 (p : Pattern) (guard : d5849 p = 1) : d2461 p ≤ (0 : Int) + d3971 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2461, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20259 p hg
    simpa only [d2461, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2461, d3971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20215 p hg
    simpa only [d2461, d3971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20443 (p : Pattern) (guard : d5849 p = 1) : d2462 p ≤ (0 : Int) + d3972 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2462, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d2462, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2462, d3972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20442 p hg
    simpa only [d2462, d3972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20444 (p : Pattern) (guard : d5849 p = 1) : d2463 p ≤ (0 : Int) + d3973 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2463, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20443 p hg
    simpa only [d2463, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2463, d3973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20416 p hg
    simpa only [d2463, d3973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20445 (p : Pattern) (guard : d5849 p = 1) : d2464 p ≤ (0 : Int) + d3974 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2464, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20292 p hg
    simpa only [d2464, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2464, d3974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2464, d3974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20446 (p : Pattern) (guard : d5849 p = 1) : d2465 p ≤ (0 : Int) + d3975 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2465, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20445 p hg
    simpa only [d2465, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2465, d3975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2465, d3975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20447 (p : Pattern) (guard : d5849 p = 1) : d2466 p ≤ (0 : Int) + d3976 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2466, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20446 p hg
    simpa only [d2466, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2466, d3976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2466, d3976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20448 (p : Pattern) (guard : d5849 p = 1) : d2467 p ≤ (0 : Int) + d3977 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2467, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20444 p hg
    simpa only [d2467, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2467, d3977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20447 p hg
    simpa only [d2467, d3977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20449 (p : Pattern) (guard : d5849 p = 1) : d2468 p ≤ (0 : Int) + d3978 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2468, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20441 p hg
    simpa only [d2468, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2468, d3978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20448 p hg
    simpa only [d2468, d3978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20450 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3979 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20451 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3980 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20202 p hg
    simpa only [d5849, d2336, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, d3980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20450 p hg
    simpa only [d5849, d2336, d3980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20452 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d3981 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20239 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20451 p hg
    simpa only [d3981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20453 (p : Pattern) (guard : d5849 p = 1) : d2337 p ≤ (0 : Int) + d3982 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20244 p hg
    simpa only [d2337, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2337, d3982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2337, d3982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20454 (p : Pattern) (guard : d5849 p = 1) : d2354 p ≤ (0 : Int) + d3983 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20452 p hg
    simpa only [d2354, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2354, d3983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20453 p hg
    simpa only [d2354, d3983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20455 (p : Pattern) (guard : d5849 p = 1) : d2377 p ≤ (0 : Int) + d3984 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20436 p hg
    simpa only [d2377, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2377, d3984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d2377, d3984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20456 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3985 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20457 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3986 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20221 p hg
    simpa only [d5849, d2328, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d5849, d2328, d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20458 (p : Pattern) (guard : d5849 p = 1) : d2328 p ≤ (0 : Int) + d3987 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20171 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20459 (p : Pattern) (guard : d5849 p = 1) : d2329 p ≤ (0 : Int) + d3988 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20176 p hg
    simpa only [d2329, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2329, d3988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20460 (p : Pattern) (guard : d5849 p = 1) : d2330 p ≤ (0 : Int) + d3989 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d2330, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d2330, d3989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20461 (p : Pattern) (guard : d5849 p = 1) : d2444 p ≤ (0 : Int) + d3990 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20460 p hg
    simpa only [d2444, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2444, d3990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20462 (p : Pattern) (guard : d5849 p = 1) : d2454 p ≤ (0 : Int) + d3991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2454, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d2454, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2454, d3991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20461 p hg
    simpa only [d2454, d3991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20463 (p : Pattern) (guard : d5849 p = 1) : d2329 p ≤ (0 : Int) + d3992 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d2329, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2329, d3992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2329, d3992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20464 (p : Pattern) (guard : d5849 p = 1) : d2330 p ≤ (0 : Int) + d3993 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d2330, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2330, d3993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20463 p hg
    simpa only [d2330, d3993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20465 (p : Pattern) (guard : d5849 p = 1) : d2444 p ≤ (0 : Int) + d3994 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20464 p hg
    simpa only [d2444, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2444, d3994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2444, d3994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20466 (p : Pattern) (guard : d5849 p = 1) : d2446 p ≤ (0 : Int) + d3995 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d2446, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2446, d3995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2446, d3995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20467 (p : Pattern) (guard : d5849 p = 1) : d2455 p ≤ (0 : Int) + d3996 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2455, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d2455, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2455, d3996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20466 p hg
    simpa only [d2455, d3996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20468 (p : Pattern) (guard : d5849 p = 1) : d2469 p ≤ (0 : Int) + d3997 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2469, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20224 p hg
    simpa only [d2469, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2469, d3997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20215 p hg
    simpa only [d2469, d3997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20469 (p : Pattern) (guard : d5849 p = 1) : d2470 p ≤ (0 : Int) + d3998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2470, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20468 p hg
    simpa only [d2470, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2470, d3998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20225 p hg
    simpa only [d2470, d3998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20470 (p : Pattern) (guard : d5849 p = 1) : d2471 p ≤ (0 : Int) + d3999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2471, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20469 p hg
    simpa only [d2471, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2471, d3999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20446 p hg
    simpa only [d2471, d3999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20471 (p : Pattern) (guard : d5849 p = 1) : d2472 p ≤ (0 : Int) + d4000 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2472, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19958 p hg
    simpa only [d2472, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2472, d4000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2472, d4000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20472 (p : Pattern) (guard : d5849 p = 1) : d2473 p ≤ (0 : Int) + d4001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2473, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20470 p hg
    simpa only [d2473, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2473, d4001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20471 p hg
    simpa only [d2473, d4001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20473 (p : Pattern) (guard : d5849 p = 1) : d2474 p ≤ (0 : Int) + d4002 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2474, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d2474, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2474, d4002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20472 p hg
    simpa only [d2474, d4002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20474 (p : Pattern) (guard : d5849 p = 1) : d2475 p ≤ (0 : Int) + d4003 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2475, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20449 p hg
    simpa only [d2475, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2475, d4003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d2475, d4003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20475 (p : Pattern) (guard : d5849 p = 1) : d2327 p ≤ (0 : Int) + d4004 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20277 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20280 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20476 (p : Pattern) (guard : d5849 p = 1) : d2476 p ≤ (0 : Int) + d4005 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2476, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d2476, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2476, d4005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2476, d4005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20477 (p : Pattern) (guard : d5849 p = 1) : d2477 p ≤ (0 : Int) + d4006 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2477, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20475 p hg
    simpa only [d2477, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2477, d4006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20476 p hg
    simpa only [d2477, d4006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20478 (p : Pattern) (guard : d5849 p = 1) : d2478 p ≤ (0 : Int) + d4007 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2478, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d2478, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2478, d4007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20302 p hg
    simpa only [d2478, d4007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20479 (p : Pattern) (guard : d5849 p = 1) : d2479 p ≤ (0 : Int) + d4008 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2479, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20478 p hg
    simpa only [d2479, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2479, d4008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20306 p hg
    simpa only [d2479, d4008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20480 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4009 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20481 (p : Pattern) (guard : d5849 p = 1) : d2336 p ≤ (0 : Int) + d4010 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20202 p hg
    simpa only [d5849, d2336, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20480 p hg
    simpa only [d5849, d2336, d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20482 (p : Pattern) (guard : d5849 p = 1) : d2337 p ≤ (0 : Int) + d4011 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2337, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20481 p hg
    simpa only [d2337, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2337, d4011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2337, d4011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20483 (p : Pattern) (guard : d5849 p = 1) : d2354 p ≤ (0 : Int) + d4012 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2354, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20259 p hg
    simpa only [d2354, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2354, d4012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20482 p hg
    simpa only [d2354, d4012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20484 (p : Pattern) (guard : d5849 p = 1) : d2354 p ≤ (0 : Int) + d4013 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20483 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20485 (p : Pattern) (guard : d5849 p = 1) : d2480 p ≤ (0 : Int) + d4014 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2480, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20484 p hg
    simpa only [d2480, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2480, d4014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20422 p hg
    simpa only [d2480, d4014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20486 (p : Pattern) (guard : d5849 p = 1) : d2481 p ≤ (0 : Int) + d4015 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2481, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20485 p hg
    simpa only [d2481, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2481, d4015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20305 p hg
    simpa only [d2481, d4015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20487 (p : Pattern) (guard : d5849 p = 1) : d2482 p ≤ (0 : Int) + d4016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2482, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20045 p hg
    simpa only [d2482, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2482, d4016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2482, d4016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20488 (p : Pattern) (guard : d5849 p = 1) : d2483 p ≤ (0 : Int) + d4017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2483, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20487 p hg
    simpa only [d2483, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2483, d4017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2483, d4017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20489 (p : Pattern) (guard : d5849 p = 1) : d2484 p ≤ (0 : Int) + d4018 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2484, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20486 p hg
    simpa only [d2484, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2484, d4018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20488 p hg
    simpa only [d2484, d4018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20490 (p : Pattern) (guard : d5849 p = 1) : d2485 p ≤ (0 : Int) + d4019 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2485, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20479 p hg
    simpa only [d2485, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2485, d4019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20489 p hg
    simpa only [d2485, d4019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20491 (p : Pattern) (guard : d5849 p = 1) : d2486 p ≤ (0 : Int) + d4020 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2486, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20474 p hg
    simpa only [d2486, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2486, d4020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20490 p hg
    simpa only [d2486, d4020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20492 (p : Pattern) (guard : d5849 p = 1) : d2487 p ≤ (0 : Int) + d4021 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2487, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d2487, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2487, d4021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2487, d4021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20493 (p : Pattern) (guard : d5849 p = 1) : d2488 p ≤ (0 : Int) + d4022 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2488, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20475 p hg
    simpa only [d2488, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2488, d4022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20492 p hg
    simpa only [d2488, d4022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20494 (p : Pattern) (guard : d5849 p = 1) : d2489 p ≤ (0 : Int) + d4023 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2489, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d2489, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2489, d4023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20044 p hg
    simpa only [d2489, d4023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20495 (p : Pattern) (guard : d5849 p = 1) : d2490 p ≤ (0 : Int) + d4024 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2490, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20494 p hg
    simpa only [d2490, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2490, d4024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2490, d4024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20496 (p : Pattern) (guard : d5849 p = 1) : d2491 p ≤ (0 : Int) + d4025 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2491, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20493 p hg
    simpa only [d2491, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2491, d4025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d2491, d4025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20497 (p : Pattern) (guard : d5849 p = 1) : d2492 p ≤ (0 : Int) + d4026 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2492, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20293 p hg
    simpa only [d2492, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2492, d4026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20010 p hg
    simpa only [d2492, d4026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20498 (p : Pattern) (guard : d5849 p = 1) : d2493 p ≤ (0 : Int) + d4027 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2493, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20497 p hg
    simpa only [d2493, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2493, d4027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2493, d4027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20499 (p : Pattern) (guard : d5849 p = 1) : d2494 p ≤ (0 : Int) + d4028 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2494, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20498 p hg
    simpa only [d2494, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2494, d4028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2494, d4028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20500 (p : Pattern) (guard : d5849 p = 1) : d2495 p ≤ (0 : Int) + d4029 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2495, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20496 p hg
    simpa only [d2495, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2495, d4029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20499 p hg
    simpa only [d2495, d4029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20501 (p : Pattern) (guard : d5849 p = 1) : d2496 p ≤ (0 : Int) + d4030 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2496, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20500 p hg
    simpa only [d2496, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2496, d4030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20489 p hg
    simpa only [d2496, d4030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20502 (p : Pattern) (guard : d5849 p = 1) : d2497 p ≤ (0 : Int) + d4031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2497, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20501 p hg
    simpa only [d2497, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2497, d4031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2497, d4031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20503 (p : Pattern) (guard : d5849 p = 1) : d2498 p ≤ (0 : Int) + d4032 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2498, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20491 p hg
    simpa only [d2498, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2498, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20502 p hg
    simpa only [d2498, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20504 (p : Pattern) (guard : d5849 p = 1) : d2499 p ≤ (0 : Int) + d4033 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2499, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20430 p hg
    simpa only [d2499, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2499, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20503 p hg
    simpa only [d2499, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20505 (p : Pattern) (guard : d5849 p = 1) : d2500 p ≤ (0 : Int) + d4034 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2500, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20100 p hg
    simpa only [d2500, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2500, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20504 p hg
    simpa only [d2500, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20506 (p : Pattern) (guard : d5849 p = 1) : d2501 p ≤ (0 : Int) + d4035 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2501, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20411 p hg
    simpa only [d2501, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2501, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20505 p hg
    simpa only [d2501, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20507 (p : Pattern) (guard : d5849 p = 1) : d2502 p ≤ (0 : Int) + d4036 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2502, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20330 p hg
    simpa only [d2502, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2502, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20506 p hg
    simpa only [d2502, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20508 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20509 (p : Pattern) (guard : d5850 p = 1) : d2503 p ≤ (0 : Int) + d3541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2503, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19827 p hg
    simpa only [d5850, d2503, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2503, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20508 p hg
    simpa only [d5850, d2503, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20510 (p : Pattern) (guard : d5850 p = 1) : d2504 p ≤ (0 : Int) + d13 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19882 p hg
    simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20511 (p : Pattern) (guard : d5850 p = 1) : d2505 p ≤ (0 : Int) + d3542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2505, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20509 p hg
    simpa only [d2505, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2505, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2505, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20512 (p : Pattern) (guard : d5850 p = 1) : d2504 p ≤ (0 : Int) + d3544 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2504, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5850, d2504, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2504, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19838 p hg
    simpa only [d5850, d2504, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20513 (p : Pattern) (guard : d5843 p = 1) : d1769 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1769, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1769, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1769, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d1769, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20514 (p : Pattern) (guard : d5843 p = 1) : d1770 p ≤ (0 : Int) + d3543 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1770, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20513 p hg
    simpa only [d1770, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1770, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d1770, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20515 (p : Pattern) (guard : d5850 p = 1) : d2506 p ≤ (0 : Int) + d3543 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19838 p hg
    simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20516 (p : Pattern) (guard : d5850 p = 1) : d2507 p ≤ (0 : Int) + d3545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20512 p hg
    simpa only [d2507, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20515 p hg
    simpa only [d2507, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20517 (p : Pattern) (guard : d5850 p = 1) : d2508 p ≤ (0 : Int) + d3546 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2508, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20511 p hg
    simpa only [d2508, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2508, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2508, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20518 (p : Pattern) (guard : d5850 p = 1) : d2504 p ≤ (0 : Int) + d3548 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2504, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5850, d2504, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2504, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19844 p hg
    simpa only [d5850, d2504, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20519 (p : Pattern) (guard : d5843 p = 1) : d1683 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1683, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d1683, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1683, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d1683, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20520 (p : Pattern) (guard : d5843 p = 1) : d1684 p ≤ (0 : Int) + d3547 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1684, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20519 p hg
    simpa only [d1684, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1684, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19917 p hg
    simpa only [d1684, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20521 (p : Pattern) (guard : d5850 p = 1) : d2509 p ≤ (0 : Int) + d3547 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20520 p hg
    simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19844 p hg
    simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20522 (p : Pattern) (guard : d5850 p = 1) : d2510 p ≤ (0 : Int) + d3549 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2510, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20518 p hg
    simpa only [d2510, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2510, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20521 p hg
    simpa only [d2510, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20523 (p : Pattern) (guard : d5850 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare20524 (p : Pattern) (guard : d5850 p = 1) : d2511 p ≤ (0 : Int) + d3550 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2511, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20522 p hg
    simpa only [d2511, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2511, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2511, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20525 (p : Pattern) (guard : d5850 p = 1) : d2512 p ≤ (0 : Int) + d3551 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2512, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20517 p hg
    simpa only [d2512, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2512, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d2512, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20526 (p : Pattern) (guard : d0 p = 1) : d327 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20527 (p : Pattern) (guard : d5850 p = 1) : d2513 p ≤ (0 : Int) + d13 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20526 p hg
    simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20528 (p : Pattern) (guard : d5850 p = 1) : d2514 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20527 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20529 (p : Pattern) (guard : d5850 p = 1) : d2515 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2515, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20528 p hg
    simpa only [d2515, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2515, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2515, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20530 (p : Pattern) (guard : d5850 p = 1) : d2516 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2516, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20529 p hg
    simpa only [d2516, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2516, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d2516, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20531 (p : Pattern) (guard : d5850 p = 1) : d2517 p ≤ (0 : Int) + d3554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2517, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20525 p hg
    simpa only [d2517, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2517, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20530 p hg
    simpa only [d2517, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20532 (p : Pattern) (guard : d5850 p = 1) : d2518 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2518, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2518, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20533 (p : Pattern) (guard : d5850 p = 1) : d2519 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2519, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20532 p hg
    simpa only [d2519, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2519, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d2519, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20534 (p : Pattern) (guard : d5850 p = 1) : d2520 p ≤ (0 : Int) + d17 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20535 (p : Pattern) (guard : d5850 p = 1) : d2520 p ≤ (0 : Int) + d3556 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2520, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5850, d2520, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2520, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19870 p hg
    simpa only [d5850, d2520, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20536 (p : Pattern) (guard : d5843 p = 1) : d1794 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1794, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1794, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1794, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d5843, d1794, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20537 (p : Pattern) (guard : d5843 p = 1) : d1795 p ≤ (0 : Int) + d3555 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1795, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20536 p hg
    simpa only [d1795, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1795, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d1795, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20538 (p : Pattern) (guard : d5850 p = 1) : d2521 p ≤ (0 : Int) + d3555 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19870 p hg
    simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20539 (p : Pattern) (guard : d5850 p = 1) : d2522 p ≤ (0 : Int) + d3557 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20535 p hg
    simpa only [d2522, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20538 p hg
    simpa only [d2522, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20540 (p : Pattern) (guard : d5850 p = 1) : d2523 p ≤ (0 : Int) + d3558 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20534 p hg
    simpa only [d2523, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20539 p hg
    simpa only [d2523, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20541 (p : Pattern) (guard : d5850 p = 1) : d2520 p ≤ (0 : Int) + d3560 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2520, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5850, d2520, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2520, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19876 p hg
    simpa only [d5850, d2520, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20542 (p : Pattern) (guard : d5843 p = 1) : d1693 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1693, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d1693, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1693, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1693, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20543 (p : Pattern) (guard : d5843 p = 1) : d1694 p ≤ (0 : Int) + d3559 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1694, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20542 p hg
    simpa only [d1694, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1694, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d1694, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20544 (p : Pattern) (guard : d5850 p = 1) : d2524 p ≤ (0 : Int) + d3559 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20543 p hg
    simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19876 p hg
    simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20545 (p : Pattern) (guard : d5850 p = 1) : d2525 p ≤ (0 : Int) + d3561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2525, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20541 p hg
    simpa only [d2525, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2525, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20544 p hg
    simpa only [d2525, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20546 (p : Pattern) (guard : d5850 p = 1) : d2526 p ≤ (0 : Int) + d3562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2526, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20545 p hg
    simpa only [d2526, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2526, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2526, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20547 (p : Pattern) (guard : d5850 p = 1) : d2527 p ≤ (0 : Int) + d3563 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2527, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20540 p hg
    simpa only [d2527, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2527, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20546 p hg
    simpa only [d2527, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20548 (p : Pattern) (guard : d5850 p = 1) : d2528 p ≤ (0 : Int) + d3564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2528, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d2528, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2528, d3564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20547 p hg
    simpa only [d2528, d3564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20549 (p : Pattern) (guard : d5850 p = 1) : d2529 p ≤ (0 : Int) + d3565 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2529, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20531 p hg
    simpa only [d2529, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2529, d3565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d2529, d3565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20550 (p : Pattern) (guard : d5850 p = 1) : d2530 p ≤ (0 : Int) + d23 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20551 (p : Pattern) (guard : d5850 p = 1) : d2530 p ≤ (0 : Int) + d3566 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2530, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5850, d2530, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2530, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5850, d2530, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20552 (p : Pattern) (guard : d5843 p = 1) : d356 p ≤ (0 : Int) + d356 p := by
  omega
theorem compare20553 (p : Pattern) (guard : d5850 p = 1) : d357 p ≤ (0 : Int) + d356 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20554 (p : Pattern) (guard : d5850 p = 1) : d2531 p ≤ (0 : Int) + d3567 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2531, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20551 p hg
    simpa only [d2531, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2531, d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20553 p hg
    simpa only [d2531, d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20555 (p : Pattern) (guard : d5850 p = 1) : d2532 p ≤ (0 : Int) + d3568 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2532, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20550 p hg
    simpa only [d2532, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2532, d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20554 p hg
    simpa only [d2532, d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20556 (p : Pattern) (guard : d5850 p = 1) : d2530 p ≤ (0 : Int) + d3570 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2530, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19890 p hg
    simpa only [d5850, d2530, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2530, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19902 p hg
    simpa only [d5850, d2530, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20557 (p : Pattern) (guard : d5843 p = 1) : d1701 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1701, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14547 p hg
    simpa only [d5843, d1701, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1701, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19937 p hg
    simpa only [d5843, d1701, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20558 (p : Pattern) (guard : d5843 p = 1) : d1702 p ≤ (0 : Int) + d3569 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1702, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20557 p hg
    simpa only [d1702, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1702, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d1702, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20559 (p : Pattern) (guard : d5850 p = 1) : d2533 p ≤ (0 : Int) + d3569 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20558 p hg
    simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19902 p hg
    simpa only [d5850, d2533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20560 (p : Pattern) (guard : d5850 p = 1) : d2534 p ≤ (0 : Int) + d3571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2534, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20556 p hg
    simpa only [d2534, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2534, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20559 p hg
    simpa only [d2534, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20561 (p : Pattern) (guard : d5850 p = 1) : d2535 p ≤ (0 : Int) + d3572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2535, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20560 p hg
    simpa only [d2535, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2535, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2535, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20562 (p : Pattern) (guard : d5850 p = 1) : d2536 p ≤ (0 : Int) + d3573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2536, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20555 p hg
    simpa only [d2536, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2536, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20561 p hg
    simpa only [d2536, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20563 (p : Pattern) (guard : d5850 p = 1) : d2537 p ≤ (0 : Int) + d3574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2537, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20562 p hg
    simpa only [d2537, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2537, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2537, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20564 (p : Pattern) (guard : d5850 p = 1) : d2538 p ≤ (0 : Int) + d3575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2538, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d2538, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2538, d3575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20563 p hg
    simpa only [d2538, d3575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20565 (p : Pattern) (guard : d5850 p = 1) : d2539 p ≤ (0 : Int) + d3576 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2539, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20549 p hg
    simpa only [d2539, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2539, d3576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20564 p hg
    simpa only [d2539, d3576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20566 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20567 (p : Pattern) (guard : d5850 p = 1) : d2504 p ≤ (0 : Int) + d3578 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2504, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5850, d2504, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2504, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20566 p hg
    simpa only [d5850, d2504, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20568 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3579 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20569 (p : Pattern) (guard : d5850 p = 1) : d2506 p ≤ (0 : Int) + d3580 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2506, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d5850, d2506, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2506, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20568 p hg
    simpa only [d5850, d2506, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20570 (p : Pattern) (guard : d5850 p = 1) : d2507 p ≤ (0 : Int) + d3581 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20567 p hg
    simpa only [d2507, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20569 p hg
    simpa only [d2507, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20571 (p : Pattern) (guard : d5850 p = 1) : d2518 p ≤ (0 : Int) + d3582 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2518, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20570 p hg
    simpa only [d2518, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20572 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3583 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20573 (p : Pattern) (guard : d5850 p = 1) : d2540 p ≤ (0 : Int) + d3584 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2540, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5850, d2540, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2540, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20572 p hg
    simpa only [d5850, d2540, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20574 (p : Pattern) (guard : d5843 p = 1) : d1713 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1713, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1713, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1713, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19926 p hg
    simpa only [d5843, d1713, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20575 (p : Pattern) (guard : d5843 p = 1) : d1714 p ≤ (0 : Int) + d3585 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1714, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20574 p hg
    simpa only [d1714, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1714, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d1714, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20576 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20577 (p : Pattern) (guard : d5850 p = 1) : d2541 p ≤ (0 : Int) + d3586 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2541, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d5850, d2541, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2541, d3586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20576 p hg
    simpa only [d5850, d2541, d3586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20578 (p : Pattern) (guard : d5850 p = 1) : d2542 p ≤ (0 : Int) + d3587 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20573 p hg
    simpa only [d2542, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20577 p hg
    simpa only [d2542, d3587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20579 (p : Pattern) (guard : d5850 p = 1) : d2543 p ≤ (0 : Int) + d3588 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20578 p hg
    simpa only [d2543, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2543, d3588, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
