/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons135
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19040 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19041 (p : Pattern) (guard : d5503 p = 1) : d2229 p ≤ (0 : Int) + d2566 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2229, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14905 p hg
    simpa only [d5503, d2229, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2229, d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19040 p hg
    simpa only [d5503, d2229, d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19042 (p : Pattern) (guard : d5503 p = 1) : d2230 p ≤ (0 : Int) + d2567 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2230, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19041 p hg
    simpa only [d2230, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2230, d2567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2230, d2567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19043 (p : Pattern) (guard : d5503 p = 1) : d2231 p ≤ (0 : Int) + d2568 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2231, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19042 p hg
    simpa only [d2231, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2231, d2568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2231, d2568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19044 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2540 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19045 (p : Pattern) (guard : d5503 p = 1) : d2209 p ≤ (0 : Int) + d2540 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19044 p hg
    simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19046 (p : Pattern) (guard : d5503 p = 1) : d2209 p ≤ (0 : Int) + d2569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19045 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19018 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19047 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2570 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19048 (p : Pattern) (guard : d5503 p = 1) : d2209 p ≤ (0 : Int) + d2571 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2209, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14878 p hg
    simpa only [d5503, d2209, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2209, d2571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19047 p hg
    simpa only [d5503, d2209, d2571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19049 (p : Pattern) (guard : d5503 p = 1) : d2210 p ≤ (0 : Int) + d2572 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2210, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19048 p hg
    simpa only [d2210, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2210, d2572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2210, d2572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19050 (p : Pattern) (guard : d5503 p = 1) : d2232 p ≤ (0 : Int) + d2573 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2232, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d2232, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2232, d2573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19049 p hg
    simpa only [d2232, d2573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19051 (p : Pattern) (guard : d5503 p = 1) : d2233 p ≤ (0 : Int) + d2574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2233, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19043 p hg
    simpa only [d2233, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2233, d2574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19050 p hg
    simpa only [d2233, d2574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19052 (p : Pattern) (guard : d5503 p = 1) : d2234 p ≤ (0 : Int) + d2575 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2234, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18997 p hg
    simpa only [d2234, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2234, d2575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19013 p hg
    simpa only [d2234, d2575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19053 (p : Pattern) (guard : d5503 p = 1) : d2235 p ≤ (0 : Int) + d2576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2235, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19051 p hg
    simpa only [d2235, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2235, d2576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19052 p hg
    simpa only [d2235, d2576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19054 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19055 (p : Pattern) (guard : d5503 p = 1) : d2236 p ≤ (0 : Int) + d2577 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19054 p hg
    simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19056 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19057 (p : Pattern) (guard : d5503 p = 1) : d2236 p ≤ (0 : Int) + d2578 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2236, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14919 p hg
    simpa only [d5503, d2236, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2236, d2578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19056 p hg
    simpa only [d5503, d2236, d2578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19058 (p : Pattern) (guard : d5503 p = 1) : d2236 p ≤ (0 : Int) + d2579 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19055 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19057 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19059 (p : Pattern) (guard : d5503 p = 1) : d2237 p ≤ (0 : Int) + d2580 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2237, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19057 p hg
    simpa only [d2237, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2237, d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2237, d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19060 (p : Pattern) (guard : d5503 p = 1) : d2238 p ≤ (0 : Int) + d2581 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2238, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19058 p hg
    simpa only [d2238, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2238, d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19059 p hg
    simpa only [d2238, d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19061 (p : Pattern) (guard : d5503 p = 1) : d2239 p ≤ (0 : Int) + d2582 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2239, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18997 p hg
    simpa only [d2239, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2239, d2582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d2239, d2582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19062 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2551 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19063 (p : Pattern) (guard : d5503 p = 1) : d2216 p ≤ (0 : Int) + d2551 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14889 p hg
    simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19062 p hg
    simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19064 (p : Pattern) (guard : d5503 p = 1) : d2216 p ≤ (0 : Int) + d2583 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19063 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19027 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19065 (p : Pattern) (guard : d5503 p = 1) : d2240 p ≤ (0 : Int) + d2584 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2240, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19064 p hg
    simpa only [d2240, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2240, d2584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19028 p hg
    simpa only [d2240, d2584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19066 (p : Pattern) (guard : d5503 p = 1) : d2241 p ≤ (0 : Int) + d2585 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2241, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2241, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2241, d2585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2241, d2585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19067 (p : Pattern) (guard : d5503 p = 1) : d2242 p ≤ (0 : Int) + d2586 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2242, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19061 p hg
    simpa only [d2242, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2242, d2586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d2242, d2586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19068 (p : Pattern) (guard : d5503 p = 1) : d2243 p ≤ (0 : Int) + d2587 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2243, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19053 p hg
    simpa only [d2243, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2243, d2587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19067 p hg
    simpa only [d2243, d2587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19069 (p : Pattern) (guard : d5503 p = 1) : d2244 p ≤ (0 : Int) + d2588 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2244, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d2244, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2244, d2588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2244, d2588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19070 (p : Pattern) (guard : d5503 p = 1) : d2245 p ≤ (0 : Int) + d2589 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2245, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19024 p hg
    simpa only [d2245, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2245, d2589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19069 p hg
    simpa only [d2245, d2589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19071 (p : Pattern) (guard : d5503 p = 1) : d2246 p ≤ (0 : Int) + d2590 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2246, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d2246, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2246, d2590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19035 p hg
    simpa only [d2246, d2590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19072 (p : Pattern) (guard : d5503 p = 1) : d2247 p ≤ (0 : Int) + d2591 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2247, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19070 p hg
    simpa only [d2247, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2247, d2591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19071 p hg
    simpa only [d2247, d2591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19073 (p : Pattern) (guard : d5503 p = 1) : d2248 p ≤ (0 : Int) + d2592 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2248, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19058 p hg
    simpa only [d2248, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2248, d2592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2248, d2592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19074 (p : Pattern) (guard : d5503 p = 1) : d2249 p ≤ (0 : Int) + d2593 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2249, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d2249, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2249, d2593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19073 p hg
    simpa only [d2249, d2593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19075 (p : Pattern) (guard : d5503 p = 1) : d2250 p ≤ (0 : Int) + d2594 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2250, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19064 p hg
    simpa only [d2250, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2250, d2594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2250, d2594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19076 (p : Pattern) (guard : d5503 p = 1) : d2251 p ≤ (0 : Int) + d2595 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2251, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19075 p hg
    simpa only [d2251, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2251, d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2251, d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19077 (p : Pattern) (guard : d5503 p = 1) : d2252 p ≤ (0 : Int) + d2596 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2252, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19074 p hg
    simpa only [d2252, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2252, d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19076 p hg
    simpa only [d2252, d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19078 (p : Pattern) (guard : d5503 p = 1) : d2253 p ≤ (0 : Int) + d2597 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2253, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19072 p hg
    simpa only [d2253, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2253, d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19077 p hg
    simpa only [d2253, d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19079 (p : Pattern) (guard : d5503 p = 1) : d2254 p ≤ (0 : Int) + d2598 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2254, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19068 p hg
    simpa only [d2254, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2254, d2598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19078 p hg
    simpa only [d2254, d2598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19080 (p : Pattern) (guard : d5503 p = 1) : d2255 p ≤ (0 : Int) + d2599 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2255, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19039 p hg
    simpa only [d2255, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2255, d2599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19079 p hg
    simpa only [d2255, d2599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19081 (p : Pattern) (guard : d5503 p = 1) : d2187 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2187, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2187, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2187, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2187, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19082 (p : Pattern) (guard : d5503 p = 1) : d2201 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2201, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d2201, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2201, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19081 p hg
    simpa only [d2201, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19083 (p : Pattern) (guard : d5503 p = 1) : d2197 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2197, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18992 p hg
    simpa only [d2197, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2197, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2197, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19084 (p : Pattern) (guard : d5503 p = 1) : d2198 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2198, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18993 p hg
    simpa only [d2198, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2198, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19083 p hg
    simpa only [d2198, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19085 (p : Pattern) (guard : d5503 p = 1) : d2202 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2202, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d2202, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2202, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d2202, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19086 (p : Pattern) (guard : d5503 p = 1) : d2256 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2256, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d2256, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2256, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19085 p hg
    simpa only [d2256, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19087 (p : Pattern) (guard : d5503 p = 1) : d2204 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2204, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19008 p hg
    simpa only [d2204, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2204, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2204, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19088 (p : Pattern) (guard : d5503 p = 1) : d2205 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2205, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19009 p hg
    simpa only [d2205, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2205, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19087 p hg
    simpa only [d2205, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19089 (p : Pattern) (guard : d5503 p = 1) : d2206 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2206, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d2206, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2206, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2206, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19090 (p : Pattern) (guard : d5503 p = 1) : d2207 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2207, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19085 p hg
    simpa only [d2207, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2207, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19089 p hg
    simpa only [d2207, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19091 (p : Pattern) (guard : d5503 p = 1) : d2257 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2257, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19086 p hg
    simpa only [d2257, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2257, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19090 p hg
    simpa only [d2257, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19092 (p : Pattern) (guard : d5503 p = 1) : d2232 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2232, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d2232, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2232, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19019 p hg
    simpa only [d2232, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19093 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2545 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19094 (p : Pattern) (guard : d5503 p = 1) : d2212 p ≤ (0 : Int) + d2545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19093 p hg
    simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19095 (p : Pattern) (guard : d5503 p = 1) : d2212 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19094 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19022 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19096 (p : Pattern) (guard : d5503 p = 1) : d2258 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2258, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19095 p hg
    simpa only [d2258, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2258, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d2258, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19097 (p : Pattern) (guard : d5503 p = 1) : d2259 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2259, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19092 p hg
    simpa only [d2259, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2259, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19096 p hg
    simpa only [d2259, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19098 (p : Pattern) (guard : d5503 p = 1) : d2260 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2260, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19097 p hg
    simpa only [d2260, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2260, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d2260, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19099 (p : Pattern) (guard : d5503 p = 1) : d2261 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2261, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19098 p hg
    simpa only [d2261, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2261, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2261, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19100 (p : Pattern) (guard : d5503 p = 1) : d2262 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2262, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19091 p hg
    simpa only [d2262, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2262, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19099 p hg
    simpa only [d2262, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19101 (p : Pattern) (guard : d5503 p = 1) : d2263 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2263, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d2263, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2263, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19092 p hg
    simpa only [d2263, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19102 (p : Pattern) (guard : d5503 p = 1) : d2234 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2234, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d2234, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2234, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d2234, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19103 (p : Pattern) (guard : d5503 p = 1) : d2264 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2264, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19101 p hg
    simpa only [d2264, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2264, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19102 p hg
    simpa only [d2264, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19104 (p : Pattern) (guard : d5503 p = 1) : d2239 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2239, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d2239, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2239, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d2239, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19105 (p : Pattern) (guard : d5503 p = 1) : d2242 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2242, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19104 p hg
    simpa only [d2242, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2242, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d2242, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19106 (p : Pattern) (guard : d5503 p = 1) : d2265 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2265, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19103 p hg
    simpa only [d2265, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2265, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19105 p hg
    simpa only [d2265, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19107 (p : Pattern) (guard : d5503 p = 1) : d2266 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2266, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19096 p hg
    simpa only [d2266, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2266, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2266, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19108 (p : Pattern) (guard : d5503 p = 1) : d2267 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2267, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19107 p hg
    simpa only [d2267, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2267, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2267, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19109 (p : Pattern) (guard : d5503 p = 1) : d2268 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2268, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19108 p hg
    simpa only [d2268, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2268, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2268, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19110 (p : Pattern) (guard : d5503 p = 1) : d2269 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2269, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19106 p hg
    simpa only [d2269, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2269, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19109 p hg
    simpa only [d2269, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19111 (p : Pattern) (guard : d5503 p = 1) : d2270 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2270, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19100 p hg
    simpa only [d2270, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2270, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19110 p hg
    simpa only [d2270, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19112 (p : Pattern) (guard : d5503 p = 1) : d2271 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2271, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19080 p hg
    simpa only [d2271, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2271, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2271, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19113 (p : Pattern) (guard : d5503 p = 1) : d2195 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2195, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18987 p hg
    simpa only [d2195, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2195, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19081 p hg
    simpa only [d2195, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19114 (p : Pattern) (guard : d5503 p = 1) : d2272 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19113 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19115 (p : Pattern) (guard : d5503 p = 1) : d2273 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2273, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19114 p hg
    simpa only [d2273, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2273, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19085 p hg
    simpa only [d2273, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19116 (p : Pattern) (guard : d5503 p = 1) : d2274 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2274, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19115 p hg
    simpa only [d2274, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2274, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19090 p hg
    simpa only [d2274, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19117 (p : Pattern) (guard : d5503 p = 1) : d2275 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2275, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19116 p hg
    simpa only [d2275, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2275, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19099 p hg
    simpa only [d2275, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19118 (p : Pattern) (guard : d5503 p = 1) : d2276 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2276, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19117 p hg
    simpa only [d2276, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2276, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19110 p hg
    simpa only [d2276, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19119 (p : Pattern) (guard : d5503 p = 1) : d2277 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2277, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d2277, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2277, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2277, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19120 (p : Pattern) (guard : d5503 p = 1) : d2278 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2278, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19119 p hg
    simpa only [d2278, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2278, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d2278, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19121 (p : Pattern) (guard : d5503 p = 1) : d2279 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2279, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d2279, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2279, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2279, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19122 (p : Pattern) (guard : d5503 p = 1) : d2280 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2280, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19120 p hg
    simpa only [d2280, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2280, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19121 p hg
    simpa only [d2280, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19123 (p : Pattern) (guard : d5503 p = 1) : d2281 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2281, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19121 p hg
    simpa only [d2281, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2281, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2281, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19124 (p : Pattern) (guard : d5503 p = 1) : d2282 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2282, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19122 p hg
    simpa only [d2282, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2282, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19123 p hg
    simpa only [d2282, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19125 (p : Pattern) (guard : d5503 p = 1) : d2283 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2283, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19123 p hg
    simpa only [d2283, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2283, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2283, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19126 (p : Pattern) (guard : d5503 p = 1) : d2284 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2284, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19124 p hg
    simpa only [d2284, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2284, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19125 p hg
    simpa only [d2284, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19127 (p : Pattern) (guard : d5503 p = 1) : d2285 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2285, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19118 p hg
    simpa only [d2285, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2285, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19126 p hg
    simpa only [d2285, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19128 (p : Pattern) (guard : d5503 p = 1) : d2286 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2286, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19112 p hg
    simpa only [d2286, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2286, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19127 p hg
    simpa only [d2286, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19129 (p : Pattern) (guard : d5503 p = 1) : d2287 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2287, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18983 p hg
    simpa only [d2287, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2287, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19003 p hg
    simpa only [d2287, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19130 (p : Pattern) (guard : d5503 p = 1) : d2288 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2288, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19129 p hg
    simpa only [d2288, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2288, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d2288, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19131 (p : Pattern) (guard : d5503 p = 1) : d2289 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2289, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19130 p hg
    simpa only [d2289, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2289, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d2289, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19132 (p : Pattern) (guard : d5503 p = 1) : d2290 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2290, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19131 p hg
    simpa only [d2290, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2290, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19038 p hg
    simpa only [d2290, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19133 (p : Pattern) (guard : d5503 p = 1) : d2263 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2263, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19003 p hg
    simpa only [d2263, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2263, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19050 p hg
    simpa only [d2263, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19134 (p : Pattern) (guard : d5503 p = 1) : d2264 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2264, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19133 p hg
    simpa only [d2264, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2264, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19052 p hg
    simpa only [d2264, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19135 (p : Pattern) (guard : d5503 p = 1) : d2265 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2265, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19134 p hg
    simpa only [d2265, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2265, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19067 p hg
    simpa only [d2265, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19136 (p : Pattern) (guard : d5503 p = 1) : d2291 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2291, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19135 p hg
    simpa only [d2291, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2291, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19078 p hg
    simpa only [d2291, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19137 (p : Pattern) (guard : d5503 p = 1) : d2292 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2292, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19132 p hg
    simpa only [d2292, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2292, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19136 p hg
    simpa only [d2292, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19138 (p : Pattern) (guard : d5503 p = 1) : d2293 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2293, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19137 p hg
    simpa only [d2293, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2293, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2293, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19139 (p : Pattern) (guard : d5503 p = 1) : d2294 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2294, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2294, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2294, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2294, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19140 (p : Pattern) (guard : d5503 p = 1) : d2295 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2295, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19138 p hg
    simpa only [d2295, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2295, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19139 p hg
    simpa only [d2295, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19141 (p : Pattern) (guard : d5503 p = 1) : d2296 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2296, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19128 p hg
    simpa only [d2296, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2296, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19140 p hg
    simpa only [d2296, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19142 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19143 (p : Pattern) (guard : d5503 p = 1) : d2297 p ≤ (0 : Int) + d2654 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2297, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15003 p hg
    simpa only [d5503, d2297, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2297, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19142 p hg
    simpa only [d5503, d2297, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19144 (p : Pattern) (guard : d5503 p = 1) : d2298 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2298, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19143 p hg
    simpa only [d2298, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2298, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18974 p hg
    simpa only [d2298, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19145 (p : Pattern) (guard : d5503 p = 1) : d2299 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2299, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19144 p hg
    simpa only [d2299, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2299, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18978 p hg
    simpa only [d2299, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19146 (p : Pattern) (guard : d5503 p = 1) : d2300 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2300, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19145 p hg
    simpa only [d2300, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2300, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18988 p hg
    simpa only [d2300, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19147 (p : Pattern) (guard : d5503 p = 1) : d2301 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2301, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19146 p hg
    simpa only [d2301, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2301, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d2301, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19148 (p : Pattern) (guard : d5503 p = 1) : d2302 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2302, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19147 p hg
    simpa only [d2302, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2302, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d2302, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19149 (p : Pattern) (guard : d5503 p = 1) : d2303 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2303, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19148 p hg
    simpa only [d2303, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2303, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19038 p hg
    simpa only [d2303, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19150 (p : Pattern) (guard : d5503 p = 1) : d2304 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2304, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18983 p hg
    simpa only [d2304, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2304, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19050 p hg
    simpa only [d2304, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19151 (p : Pattern) (guard : d5503 p = 1) : d2305 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2305, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19150 p hg
    simpa only [d2305, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2305, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19052 p hg
    simpa only [d2305, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19152 (p : Pattern) (guard : d5503 p = 1) : d2306 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2306, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19151 p hg
    simpa only [d2306, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2306, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19067 p hg
    simpa only [d2306, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19153 (p : Pattern) (guard : d5503 p = 1) : d2307 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2307, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19152 p hg
    simpa only [d2307, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2307, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19078 p hg
    simpa only [d2307, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19154 (p : Pattern) (guard : d5503 p = 1) : d2308 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2308, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19149 p hg
    simpa only [d2308, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2308, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19153 p hg
    simpa only [d2308, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19155 (p : Pattern) (guard : d5503 p = 1) : d2309 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2309, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19154 p hg
    simpa only [d2309, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2309, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2309, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19156 (p : Pattern) (guard : d5503 p = 1) : d2310 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2310, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2310, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2310, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19126 p hg
    simpa only [d2310, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19157 (p : Pattern) (guard : d5503 p = 1) : d2311 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2311, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19155 p hg
    simpa only [d2311, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2311, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19156 p hg
    simpa only [d2311, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19158 (p : Pattern) (guard : d5503 p = 1) : d2272 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18988 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19003 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19159 (p : Pattern) (guard : d5503 p = 1) : d2273 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2273, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19158 p hg
    simpa only [d2273, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2273, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d2273, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19160 (p : Pattern) (guard : d5503 p = 1) : d2274 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2274, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19159 p hg
    simpa only [d2274, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2274, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d2274, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19161 (p : Pattern) (guard : d5503 p = 1) : d2312 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2312, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19160 p hg
    simpa only [d2312, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2312, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19038 p hg
    simpa only [d2312, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19162 (p : Pattern) (guard : d5503 p = 1) : d2313 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2313, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19161 p hg
    simpa only [d2313, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2313, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19136 p hg
    simpa only [d2313, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19163 (p : Pattern) (guard : d5503 p = 1) : d2314 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2314, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19162 p hg
    simpa only [d2314, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2314, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d2314, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19164 (p : Pattern) (guard : d5503 p = 1) : d2315 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2315, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19163 p hg
    simpa only [d2315, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2315, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19139 p hg
    simpa only [d2315, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19165 (p : Pattern) (guard : d5503 p = 1) : d2316 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2316, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19157 p hg
    simpa only [d2316, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2316, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19164 p hg
    simpa only [d2316, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19166 (p : Pattern) (guard : d5503 p = 1) : d2317 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2317, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19141 p hg
    simpa only [d2317, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2317, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19165 p hg
    simpa only [d2317, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19167 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d2677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19168 (p : Pattern) (guard : d5503 p = 1) : d2318 p ≤ (0 : Int) + d2678 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2318, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15027 p hg
    simpa only [d5503, d2318, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2318, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19167 p hg
    simpa only [d5503, d2318, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19169 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2679 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19170 (p : Pattern) (guard : d5503 p = 1) : d2319 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2319, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2319, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2319, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19169 p hg
    simpa only [d5503, d2319, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19171 (p : Pattern) (guard : d5503 p = 1) : d2320 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2320, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19168 p hg
    simpa only [d2320, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2320, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d2320, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19172 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2682 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19173 (p : Pattern) (guard : d5503 p = 1) : d2319 p ≤ (0 : Int) + d2683 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2319, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2319, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2319, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19172 p hg
    simpa only [d5503, d2319, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19174 (p : Pattern) (guard : d5503 p = 1) : d2321 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2321, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19173 p hg
    simpa only [d2321, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2321, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2321, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19175 (p : Pattern) (guard : d5503 p = 1) : d2322 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2322, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19171 p hg
    simpa only [d2322, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2322, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19174 p hg
    simpa only [d2322, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19176 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d2677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19177 (p : Pattern) (guard : d5503 p = 1) : d2323 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19176 p hg
    simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19178 (p : Pattern) (guard : d5503 p = 1) : d2324 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2324, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19177 p hg
    simpa only [d2324, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2324, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d2324, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19179 (p : Pattern) (guard : d5503 p = 1) : d2325 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2325, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19178 p hg
    simpa only [d2325, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2325, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19174 p hg
    simpa only [d2325, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
