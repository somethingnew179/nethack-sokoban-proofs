/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21700 (p : Pattern) (guard : d5503 p = 1) : d2561 p ≤ (0 : Int) + d2225 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2561, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21699 p hg
    simpa only [d2561, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2561, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2561, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21701 (p : Pattern) (guard : d5503 p = 1) : d2562 p ≤ (0 : Int) + d2226 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2562, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21698 p hg
    simpa only [d2562, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2562, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21700 p hg
    simpa only [d2562, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21702 (p : Pattern) (guard : d5503 p = 1) : d2563 p ≤ (0 : Int) + d2227 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2563, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21696 p hg
    simpa only [d2563, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2563, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21701 p hg
    simpa only [d2563, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21703 (p : Pattern) (guard : d5503 p = 1) : d2564 p ≤ (0 : Int) + d2228 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2564, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d2564, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2564, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21702 p hg
    simpa only [d2564, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21704 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21705 (p : Pattern) (guard : d5503 p = 1) : d2566 p ≤ (0 : Int) + d2229 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2566, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21173 p hg
    simpa only [d5503, d2566, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2566, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21704 p hg
    simpa only [d5503, d2566, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21706 (p : Pattern) (guard : d5503 p = 1) : d2567 p ≤ (0 : Int) + d2230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2567, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21705 p hg
    simpa only [d2567, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2567, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2567, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21707 (p : Pattern) (guard : d5503 p = 1) : d2568 p ≤ (0 : Int) + d2231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2568, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21706 p hg
    simpa only [d2568, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2568, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2568, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21708 (p : Pattern) (guard : d0 p = 1) : d2540 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21709 (p : Pattern) (guard : d5503 p = 1) : d2540 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21708 p hg
    simpa only [d5503, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21710 (p : Pattern) (guard : d5503 p = 1) : d2569 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21709 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d2569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21711 (p : Pattern) (guard : d0 p = 1) : d2570 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21712 (p : Pattern) (guard : d5503 p = 1) : d2571 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2571, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, d2571, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2571, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21711 p hg
    simpa only [d5503, d2571, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21713 (p : Pattern) (guard : d5503 p = 1) : d2572 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2572, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21712 p hg
    simpa only [d2572, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2572, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2572, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21714 (p : Pattern) (guard : d5503 p = 1) : d2573 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2573, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d2573, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2573, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d2573, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21715 (p : Pattern) (guard : d5503 p = 1) : d2574 p ≤ (0 : Int) + d2233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2574, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21707 p hg
    simpa only [d2574, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2574, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d2574, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21716 (p : Pattern) (guard : d5503 p = 1) : d2575 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2575, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d2575, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2575, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d2575, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21717 (p : Pattern) (guard : d5503 p = 1) : d2576 p ≤ (0 : Int) + d2235 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2576, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d2576, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2576, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d2576, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21718 (p : Pattern) (guard : d0 p = 1) : d2577 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21719 (p : Pattern) (guard : d5503 p = 1) : d2577 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21718 p hg
    simpa only [d5503, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21720 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21721 (p : Pattern) (guard : d5503 p = 1) : d2578 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2578, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d5503, d2578, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2578, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21720 p hg
    simpa only [d5503, d2578, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21722 (p : Pattern) (guard : d5503 p = 1) : d2579 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21721 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21723 (p : Pattern) (guard : d5503 p = 1) : d2580 p ≤ (0 : Int) + d2237 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2580, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21721 p hg
    simpa only [d2580, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2580, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2580, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21724 (p : Pattern) (guard : d5503 p = 1) : d2581 p ≤ (0 : Int) + d2238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2581, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21722 p hg
    simpa only [d2581, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2581, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21723 p hg
    simpa only [d2581, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21725 (p : Pattern) (guard : d5503 p = 1) : d2582 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2582, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d2582, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2582, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d2582, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21726 (p : Pattern) (guard : d0 p = 1) : d2551 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21727 (p : Pattern) (guard : d5503 p = 1) : d2551 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d5503, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21728 (p : Pattern) (guard : d5503 p = 1) : d2583 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21727 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d2583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21729 (p : Pattern) (guard : d5503 p = 1) : d2584 p ≤ (0 : Int) + d2240 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2584, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21728 p hg
    simpa only [d2584, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2584, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21692 p hg
    simpa only [d2584, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21730 (p : Pattern) (guard : d5503 p = 1) : d2585 p ≤ (0 : Int) + d2241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2585, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2585, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2585, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2585, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21731 (p : Pattern) (guard : d5503 p = 1) : d2586 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2586, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21725 p hg
    simpa only [d2586, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2586, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d2586, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21732 (p : Pattern) (guard : d5503 p = 1) : d2587 p ≤ (0 : Int) + d2243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2587, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d2587, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2587, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21731 p hg
    simpa only [d2587, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21733 (p : Pattern) (guard : d5503 p = 1) : d2588 p ≤ (0 : Int) + d2244 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2588, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d2588, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2588, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2588, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21734 (p : Pattern) (guard : d5503 p = 1) : d2589 p ≤ (0 : Int) + d2245 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2589, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21688 p hg
    simpa only [d2589, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2589, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21733 p hg
    simpa only [d2589, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21735 (p : Pattern) (guard : d5503 p = 1) : d2590 p ≤ (0 : Int) + d2246 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2590, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d2590, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2590, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21699 p hg
    simpa only [d2590, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21736 (p : Pattern) (guard : d5503 p = 1) : d2591 p ≤ (0 : Int) + d2247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2591, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21734 p hg
    simpa only [d2591, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2591, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21735 p hg
    simpa only [d2591, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21737 (p : Pattern) (guard : d5503 p = 1) : d2592 p ≤ (0 : Int) + d2248 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2592, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21722 p hg
    simpa only [d2592, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2592, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2592, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21738 (p : Pattern) (guard : d5503 p = 1) : d2593 p ≤ (0 : Int) + d2249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2593, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d2593, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2593, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21737 p hg
    simpa only [d2593, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21739 (p : Pattern) (guard : d5503 p = 1) : d2594 p ≤ (0 : Int) + d2250 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2594, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21728 p hg
    simpa only [d2594, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2594, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2594, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21740 (p : Pattern) (guard : d5503 p = 1) : d2595 p ≤ (0 : Int) + d2251 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2595, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21739 p hg
    simpa only [d2595, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2595, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2595, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21741 (p : Pattern) (guard : d5503 p = 1) : d2596 p ≤ (0 : Int) + d2252 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2596, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21738 p hg
    simpa only [d2596, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2596, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21740 p hg
    simpa only [d2596, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21742 (p : Pattern) (guard : d5503 p = 1) : d2597 p ≤ (0 : Int) + d2253 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2597, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21736 p hg
    simpa only [d2597, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2597, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21741 p hg
    simpa only [d2597, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21743 (p : Pattern) (guard : d5503 p = 1) : d2598 p ≤ (0 : Int) + d2254 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2598, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21732 p hg
    simpa only [d2598, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2598, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21742 p hg
    simpa only [d2598, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21744 (p : Pattern) (guard : d5503 p = 1) : d2599 p ≤ (0 : Int) + d2255 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2599, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21703 p hg
    simpa only [d2599, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2599, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21743 p hg
    simpa only [d2599, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21745 (p : Pattern) (guard : d5503 p = 1) : d2600 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2600, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2600, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2600, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2600, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21746 (p : Pattern) (guard : d5503 p = 1) : d2601 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2601, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2601, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2601, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21745 p hg
    simpa only [d2601, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21747 (p : Pattern) (guard : d5503 p = 1) : d2602 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2602, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21656 p hg
    simpa only [d2602, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2602, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2602, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21748 (p : Pattern) (guard : d5503 p = 1) : d2603 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2603, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21657 p hg
    simpa only [d2603, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2603, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d2603, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21749 (p : Pattern) (guard : d5503 p = 1) : d2604 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2604, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d2604, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2604, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d2604, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21750 (p : Pattern) (guard : d5503 p = 1) : d2605 p ≤ (0 : Int) + d2256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2605, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d2605, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2605, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21749 p hg
    simpa only [d2605, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21751 (p : Pattern) (guard : d5503 p = 1) : d2606 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2606, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21672 p hg
    simpa only [d2606, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2606, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2606, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21752 (p : Pattern) (guard : d5503 p = 1) : d2607 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2607, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21673 p hg
    simpa only [d2607, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2607, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21751 p hg
    simpa only [d2607, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21753 (p : Pattern) (guard : d5503 p = 1) : d2608 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2608, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d2608, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2608, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2608, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21754 (p : Pattern) (guard : d5503 p = 1) : d2609 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2609, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21749 p hg
    simpa only [d2609, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2609, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21753 p hg
    simpa only [d2609, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21755 (p : Pattern) (guard : d5503 p = 1) : d2610 p ≤ (0 : Int) + d2257 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2610, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21750 p hg
    simpa only [d2610, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2610, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21754 p hg
    simpa only [d2610, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21756 (p : Pattern) (guard : d5503 p = 1) : d2611 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2611, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d2611, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2611, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21683 p hg
    simpa only [d2611, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21757 (p : Pattern) (guard : d0 p = 1) : d2545 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21758 (p : Pattern) (guard : d5503 p = 1) : d2545 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21757 p hg
    simpa only [d5503, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21759 (p : Pattern) (guard : d5503 p = 1) : d2612 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21758 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21686 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21760 (p : Pattern) (guard : d5503 p = 1) : d2613 p ≤ (0 : Int) + d2258 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2613, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21759 p hg
    simpa only [d2613, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2613, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21687 p hg
    simpa only [d2613, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21761 (p : Pattern) (guard : d5503 p = 1) : d2614 p ≤ (0 : Int) + d2259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2614, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21756 p hg
    simpa only [d2614, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2614, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21760 p hg
    simpa only [d2614, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21762 (p : Pattern) (guard : d5503 p = 1) : d2615 p ≤ (0 : Int) + d2260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2615, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21761 p hg
    simpa only [d2615, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2615, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d2615, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21763 (p : Pattern) (guard : d5503 p = 1) : d2616 p ≤ (0 : Int) + d2261 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2616, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21762 p hg
    simpa only [d2616, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2616, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2616, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21764 (p : Pattern) (guard : d5503 p = 1) : d2617 p ≤ (0 : Int) + d2262 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2617, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21755 p hg
    simpa only [d2617, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2617, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21763 p hg
    simpa only [d2617, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21765 (p : Pattern) (guard : d5503 p = 1) : d2618 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2618, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d2618, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2618, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21756 p hg
    simpa only [d2618, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21766 (p : Pattern) (guard : d5503 p = 1) : d2619 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2619, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d2619, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2619, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d2619, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21767 (p : Pattern) (guard : d5503 p = 1) : d2620 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2620, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21765 p hg
    simpa only [d2620, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2620, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21766 p hg
    simpa only [d2620, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21768 (p : Pattern) (guard : d5503 p = 1) : d2621 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2621, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d2621, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2621, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d2621, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21769 (p : Pattern) (guard : d5503 p = 1) : d2622 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2622, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21768 p hg
    simpa only [d2622, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2622, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d2622, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21770 (p : Pattern) (guard : d5503 p = 1) : d2623 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2623, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21767 p hg
    simpa only [d2623, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2623, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21769 p hg
    simpa only [d2623, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21771 (p : Pattern) (guard : d5503 p = 1) : d2624 p ≤ (0 : Int) + d2266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2624, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21760 p hg
    simpa only [d2624, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2624, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2624, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21772 (p : Pattern) (guard : d5503 p = 1) : d2625 p ≤ (0 : Int) + d2267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2625, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21771 p hg
    simpa only [d2625, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2625, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2625, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21773 (p : Pattern) (guard : d5503 p = 1) : d2626 p ≤ (0 : Int) + d2268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2626, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21772 p hg
    simpa only [d2626, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2626, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2626, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21774 (p : Pattern) (guard : d5503 p = 1) : d2627 p ≤ (0 : Int) + d2269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2627, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21770 p hg
    simpa only [d2627, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2627, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21773 p hg
    simpa only [d2627, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21775 (p : Pattern) (guard : d5503 p = 1) : d2628 p ≤ (0 : Int) + d2270 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2628, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21764 p hg
    simpa only [d2628, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2628, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21774 p hg
    simpa only [d2628, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21776 (p : Pattern) (guard : d5503 p = 1) : d2629 p ≤ (0 : Int) + d2271 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2629, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21744 p hg
    simpa only [d2629, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2629, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2629, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21777 (p : Pattern) (guard : d5503 p = 1) : d2601 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2601, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d2601, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2601, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21745 p hg
    simpa only [d2601, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21778 (p : Pattern) (guard : d5503 p = 1) : d2601 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21777 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21779 (p : Pattern) (guard : d5503 p = 1) : d2605 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2605, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21778 p hg
    simpa only [d2605, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2605, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21749 p hg
    simpa only [d2605, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21780 (p : Pattern) (guard : d5503 p = 1) : d2610 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2610, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21779 p hg
    simpa only [d2610, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2610, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21754 p hg
    simpa only [d2610, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21781 (p : Pattern) (guard : d5503 p = 1) : d2617 p ≤ (0 : Int) + d2275 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2617, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21780 p hg
    simpa only [d2617, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2617, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21763 p hg
    simpa only [d2617, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21782 (p : Pattern) (guard : d5503 p = 1) : d2628 p ≤ (0 : Int) + d2276 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2628, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21781 p hg
    simpa only [d2628, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2628, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21774 p hg
    simpa only [d2628, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21783 (p : Pattern) (guard : d5503 p = 1) : d2630 p ≤ (0 : Int) + d2277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2630, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d2630, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2630, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2630, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21784 (p : Pattern) (guard : d5503 p = 1) : d2631 p ≤ (0 : Int) + d2278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2631, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21783 p hg
    simpa only [d2631, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2631, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d2631, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21785 (p : Pattern) (guard : d5503 p = 1) : d2632 p ≤ (0 : Int) + d2279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2632, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d2632, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2632, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2632, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21786 (p : Pattern) (guard : d5503 p = 1) : d2633 p ≤ (0 : Int) + d2280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2633, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21784 p hg
    simpa only [d2633, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2633, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21785 p hg
    simpa only [d2633, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21787 (p : Pattern) (guard : d5503 p = 1) : d2634 p ≤ (0 : Int) + d2281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2634, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21785 p hg
    simpa only [d2634, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2634, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2634, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21788 (p : Pattern) (guard : d5503 p = 1) : d2635 p ≤ (0 : Int) + d2282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2635, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21786 p hg
    simpa only [d2635, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2635, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21787 p hg
    simpa only [d2635, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21789 (p : Pattern) (guard : d5503 p = 1) : d2636 p ≤ (0 : Int) + d2283 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2636, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21787 p hg
    simpa only [d2636, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2636, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2636, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21790 (p : Pattern) (guard : d5503 p = 1) : d2637 p ≤ (0 : Int) + d2284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2637, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21788 p hg
    simpa only [d2637, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2637, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21789 p hg
    simpa only [d2637, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21791 (p : Pattern) (guard : d5503 p = 1) : d2638 p ≤ (0 : Int) + d2285 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2638, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21782 p hg
    simpa only [d2638, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2638, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21790 p hg
    simpa only [d2638, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21792 (p : Pattern) (guard : d5503 p = 1) : d2639 p ≤ (0 : Int) + d2286 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2639, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21776 p hg
    simpa only [d2639, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2639, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21791 p hg
    simpa only [d2639, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21793 (p : Pattern) (guard : d5503 p = 1) : d2640 p ≤ (0 : Int) + d2287 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2640, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21647 p hg
    simpa only [d2640, d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2640, d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d2640, d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21794 (p : Pattern) (guard : d5503 p = 1) : d2641 p ≤ (0 : Int) + d2288 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2641, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21793 p hg
    simpa only [d2641, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2641, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d2641, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21795 (p : Pattern) (guard : d5503 p = 1) : d2642 p ≤ (0 : Int) + d2289 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2642, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21794 p hg
    simpa only [d2642, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2642, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d2642, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21796 (p : Pattern) (guard : d5503 p = 1) : d2643 p ≤ (0 : Int) + d2290 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2643, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21795 p hg
    simpa only [d2643, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2643, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21702 p hg
    simpa only [d2643, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21797 (p : Pattern) (guard : d5503 p = 1) : d2644 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2644, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d2644, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2644, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d2644, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21798 (p : Pattern) (guard : d5503 p = 1) : d2645 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2645, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21797 p hg
    simpa only [d2645, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2645, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d2645, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21799 (p : Pattern) (guard : d5503 p = 1) : d2646 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2646, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21798 p hg
    simpa only [d2646, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2646, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21731 p hg
    simpa only [d2646, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21800 (p : Pattern) (guard : d5503 p = 1) : d2647 p ≤ (0 : Int) + d2291 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2647, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21799 p hg
    simpa only [d2647, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2647, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21742 p hg
    simpa only [d2647, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21801 (p : Pattern) (guard : d5503 p = 1) : d2648 p ≤ (0 : Int) + d2292 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2648, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21796 p hg
    simpa only [d2648, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2648, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21800 p hg
    simpa only [d2648, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21802 (p : Pattern) (guard : d5503 p = 1) : d2649 p ≤ (0 : Int) + d2293 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2649, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21801 p hg
    simpa only [d2649, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2649, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2649, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21803 (p : Pattern) (guard : d5503 p = 1) : d2650 p ≤ (0 : Int) + d2294 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2650, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2650, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2650, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2650, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21804 (p : Pattern) (guard : d5503 p = 1) : d2651 p ≤ (0 : Int) + d2295 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2651, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21802 p hg
    simpa only [d2651, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2651, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21803 p hg
    simpa only [d2651, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21805 (p : Pattern) (guard : d5503 p = 1) : d2652 p ≤ (0 : Int) + d2296 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2652, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21792 p hg
    simpa only [d2652, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2652, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21804 p hg
    simpa only [d2652, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21806 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21807 (p : Pattern) (guard : d5503 p = 1) : d2654 p ≤ (0 : Int) + d2297 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2654, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21287 p hg
    simpa only [d5503, d2654, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2654, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21806 p hg
    simpa only [d5503, d2654, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21808 (p : Pattern) (guard : d5503 p = 1) : d2655 p ≤ (0 : Int) + d2298 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2655, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21807 p hg
    simpa only [d2655, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2655, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2655, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21809 (p : Pattern) (guard : d5503 p = 1) : d2656 p ≤ (0 : Int) + d2299 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2656, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21808 p hg
    simpa only [d2656, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2656, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2656, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21810 (p : Pattern) (guard : d5503 p = 1) : d2657 p ≤ (0 : Int) + d2300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2657, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21809 p hg
    simpa only [d2657, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2657, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21652 p hg
    simpa only [d2657, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21811 (p : Pattern) (guard : d5503 p = 1) : d2658 p ≤ (0 : Int) + d2301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2658, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21810 p hg
    simpa only [d2658, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2658, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d2658, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21812 (p : Pattern) (guard : d5503 p = 1) : d2659 p ≤ (0 : Int) + d2302 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2659, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21811 p hg
    simpa only [d2659, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2659, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d2659, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21813 (p : Pattern) (guard : d5503 p = 1) : d2660 p ≤ (0 : Int) + d2303 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2660, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21812 p hg
    simpa only [d2660, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2660, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21702 p hg
    simpa only [d2660, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21814 (p : Pattern) (guard : d5503 p = 1) : d2661 p ≤ (0 : Int) + d2304 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2661, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21647 p hg
    simpa only [d2661, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2661, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d2661, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21815 (p : Pattern) (guard : d5503 p = 1) : d2662 p ≤ (0 : Int) + d2305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2662, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21814 p hg
    simpa only [d2662, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2662, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d2662, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21816 (p : Pattern) (guard : d5503 p = 1) : d2663 p ≤ (0 : Int) + d2306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2663, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21815 p hg
    simpa only [d2663, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2663, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21731 p hg
    simpa only [d2663, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21817 (p : Pattern) (guard : d5503 p = 1) : d2664 p ≤ (0 : Int) + d2307 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2664, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21816 p hg
    simpa only [d2664, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2664, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21742 p hg
    simpa only [d2664, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21818 (p : Pattern) (guard : d5503 p = 1) : d2665 p ≤ (0 : Int) + d2308 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2665, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21813 p hg
    simpa only [d2665, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2665, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21817 p hg
    simpa only [d2665, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21819 (p : Pattern) (guard : d5503 p = 1) : d2666 p ≤ (0 : Int) + d2309 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2666, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21818 p hg
    simpa only [d2666, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2666, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2666, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21820 (p : Pattern) (guard : d5503 p = 1) : d2638 p ≤ (0 : Int) + d2310 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2638, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2638, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2638, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21790 p hg
    simpa only [d2638, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21821 (p : Pattern) (guard : d5503 p = 1) : d2667 p ≤ (0 : Int) + d2311 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2667, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21819 p hg
    simpa only [d2667, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2667, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21820 p hg
    simpa only [d2667, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21822 (p : Pattern) (guard : d5503 p = 1) : d2519 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21652 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21823 (p : Pattern) (guard : d5503 p = 1) : d2668 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2668, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21822 p hg
    simpa only [d2668, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2668, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d2668, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21824 (p : Pattern) (guard : d5503 p = 1) : d2669 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2669, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21823 p hg
    simpa only [d2669, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2669, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d2669, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21825 (p : Pattern) (guard : d5503 p = 1) : d2670 p ≤ (0 : Int) + d2312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2670, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21824 p hg
    simpa only [d2670, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2670, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21702 p hg
    simpa only [d2670, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21826 (p : Pattern) (guard : d5503 p = 1) : d2671 p ≤ (0 : Int) + d2313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2671, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21825 p hg
    simpa only [d2671, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2671, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21800 p hg
    simpa only [d2671, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21827 (p : Pattern) (guard : d5503 p = 1) : d2672 p ≤ (0 : Int) + d2314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2672, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21826 p hg
    simpa only [d2672, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2672, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21775 p hg
    simpa only [d2672, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21828 (p : Pattern) (guard : d5503 p = 1) : d2673 p ≤ (0 : Int) + d2315 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2673, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21827 p hg
    simpa only [d2673, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2673, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21803 p hg
    simpa only [d2673, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21829 (p : Pattern) (guard : d5503 p = 1) : d2674 p ≤ (0 : Int) + d2316 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2674, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21821 p hg
    simpa only [d2674, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2674, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21828 p hg
    simpa only [d2674, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21830 (p : Pattern) (guard : d5503 p = 1) : d2675 p ≤ (0 : Int) + d2317 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2675, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21805 p hg
    simpa only [d2675, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2675, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21829 p hg
    simpa only [d2675, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21831 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21832 (p : Pattern) (guard : d5503 p = 1) : d2678 p ≤ (0 : Int) + d2318 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2678, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21311 p hg
    simpa only [d5503, d2678, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2678, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21831 p hg
    simpa only [d5503, d2678, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21833 (p : Pattern) (guard : d0 p = 1) : d2679 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21834 (p : Pattern) (guard : d5503 p = 1) : d2680 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2680, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2680, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2680, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21833 p hg
    simpa only [d5503, d2680, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21835 (p : Pattern) (guard : d5503 p = 1) : d2681 p ≤ (0 : Int) + d2320 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2681, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21832 p hg
    simpa only [d2681, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2681, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d2681, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21836 (p : Pattern) (guard : d0 p = 1) : d2682 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21837 (p : Pattern) (guard : d5503 p = 1) : d2683 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2683, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2683, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2683, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21836 p hg
    simpa only [d5503, d2683, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21838 (p : Pattern) (guard : d5503 p = 1) : d2684 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2684, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21837 p hg
    simpa only [d2684, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2684, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2684, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21839 (p : Pattern) (guard : d5503 p = 1) : d2685 p ≤ (0 : Int) + d2322 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2685, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21835 p hg
    simpa only [d2685, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2685, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21838 p hg
    simpa only [d2685, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
