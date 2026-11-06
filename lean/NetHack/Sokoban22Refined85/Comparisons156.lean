/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons155
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21840 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21841 (p : Pattern) (guard : d5503 p = 1) : d2677 p ≤ (0 : Int) + d2323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21840 p hg
    simpa only [d5503, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21842 (p : Pattern) (guard : d5503 p = 1) : d2686 p ≤ (0 : Int) + d2324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2686, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21841 p hg
    simpa only [d2686, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2686, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d2686, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21843 (p : Pattern) (guard : d5503 p = 1) : d2687 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2687, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21842 p hg
    simpa only [d2687, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2687, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21838 p hg
    simpa only [d2687, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21844 (p : Pattern) (guard : d5503 p = 1) : d2688 p ≤ (0 : Int) + d2326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2688, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21839 p hg
    simpa only [d2688, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2688, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21843 p hg
    simpa only [d2688, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21845 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21846 (p : Pattern) (guard : d5503 p = 1) : d2677 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21845 p hg
    simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21847 (p : Pattern) (guard : d5503 p = 1) : d2686 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21846 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21848 (p : Pattern) (guard : d5503 p = 1) : d2687 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2687, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d2687, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2687, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21838 p hg
    simpa only [d2687, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21849 (p : Pattern) (guard : d0 p = 1) : d2689 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21850 (p : Pattern) (guard : d5503 p = 1) : d2689 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21849 p hg
    simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21851 (p : Pattern) (guard : d0 p = 1) : d2690 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21852 (p : Pattern) (guard : d5503 p = 1) : d2691 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2691, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, d2691, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2691, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21851 p hg
    simpa only [d5503, d2691, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21853 (p : Pattern) (guard : d5503 p = 1) : d2692 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21850 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21852 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21854 (p : Pattern) (guard : d0 p = 1) : d2693 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21855 (p : Pattern) (guard : d5503 p = 1) : d2694 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2694, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d5503, d2694, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2694, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21854 p hg
    simpa only [d5503, d2694, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21856 (p : Pattern) (guard : d5503 p = 1) : d2695 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2695, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21855 p hg
    simpa only [d2695, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2695, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2695, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21857 (p : Pattern) (guard : d5503 p = 1) : d2696 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2696, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21853 p hg
    simpa only [d2696, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2696, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21856 p hg
    simpa only [d2696, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21858 (p : Pattern) (guard : d5503 p = 1) : d2697 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2697, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21848 p hg
    simpa only [d2697, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2697, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21857 p hg
    simpa only [d2697, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21859 (p : Pattern) (guard : d5503 p = 1) : d2698 p ≤ (0 : Int) + d2332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2698, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21844 p hg
    simpa only [d2698, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2698, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21858 p hg
    simpa only [d2698, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21860 (p : Pattern) (guard : d5503 p = 1) : d2699 p ≤ (0 : Int) + d2333 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2699, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d2699, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2699, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2699, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21861 (p : Pattern) (guard : d5503 p = 1) : d2700 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2700, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21858 p hg
    simpa only [d2700, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2700, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21860 p hg
    simpa only [d2700, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21862 (p : Pattern) (guard : d5503 p = 1) : d2701 p ≤ (0 : Int) + d2335 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2701, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21859 p hg
    simpa only [d2701, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2701, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21861 p hg
    simpa only [d2701, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21863 (p : Pattern) (guard : d0 p = 1) : d2703 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21864 (p : Pattern) (guard : d5503 p = 1) : d2704 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2704, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, d2704, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2704, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21863 p hg
    simpa only [d5503, d2704, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21865 (p : Pattern) (guard : d5503 p = 1) : d2705 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2705, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21864 p hg
    simpa only [d2705, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2705, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2705, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21866 (p : Pattern) (guard : d5503 p = 1) : d2706 p ≤ (0 : Int) + d2338 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2706, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d2706, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2706, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21865 p hg
    simpa only [d2706, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21867 (p : Pattern) (guard : d0 p = 1) : d2708 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21868 (p : Pattern) (guard : d5503 p = 1) : d2709 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2709, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d5503, d2709, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2709, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21867 p hg
    simpa only [d5503, d2709, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21869 (p : Pattern) (guard : d5503 p = 1) : d2710 p ≤ (0 : Int) + d2340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2710, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21868 p hg
    simpa only [d2710, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2710, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2710, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21870 (p : Pattern) (guard : d5503 p = 1) : d2711 p ≤ (0 : Int) + d2341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2711, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d2711, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2711, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21869 p hg
    simpa only [d2711, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21871 (p : Pattern) (guard : d5503 p = 1) : d2712 p ≤ (0 : Int) + d2342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2712, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21866 p hg
    simpa only [d2712, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2712, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21870 p hg
    simpa only [d2712, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21872 (p : Pattern) (guard : d5503 p = 1) : d2713 p ≤ (0 : Int) + d2343 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2713, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d2713, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2713, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2713, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21873 (p : Pattern) (guard : d5503 p = 1) : d2714 p ≤ (0 : Int) + d2344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2714, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21853 p hg
    simpa only [d2714, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2714, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2714, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21874 (p : Pattern) (guard : d5503 p = 1) : d2715 p ≤ (0 : Int) + d2345 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2715, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21872 p hg
    simpa only [d2715, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2715, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d2715, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21875 (p : Pattern) (guard : d5503 p = 1) : d2716 p ≤ (0 : Int) + d2346 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2716, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21871 p hg
    simpa only [d2716, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2716, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21874 p hg
    simpa only [d2716, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21876 (p : Pattern) (guard : d5503 p = 1) : d2717 p ≤ (0 : Int) + d2347 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2717, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21737 p hg
    simpa only [d2717, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2717, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2717, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21877 (p : Pattern) (guard : d5503 p = 1) : d2718 p ≤ (0 : Int) + d2348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2718, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21874 p hg
    simpa only [d2718, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2718, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21876 p hg
    simpa only [d2718, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21878 (p : Pattern) (guard : d5503 p = 1) : d2719 p ≤ (0 : Int) + d2349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2719, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21875 p hg
    simpa only [d2719, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2719, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21877 p hg
    simpa only [d2719, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21879 (p : Pattern) (guard : d5503 p = 1) : d2720 p ≤ (0 : Int) + d2350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2720, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21862 p hg
    simpa only [d2720, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2720, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21878 p hg
    simpa only [d2720, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21880 (p : Pattern) (guard : d0 p = 1) : d2677 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21881 (p : Pattern) (guard : d5503 p = 1) : d2722 p ≤ (0 : Int) + d2351 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2722, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d5503, d2722, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2722, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21880 p hg
    simpa only [d5503, d2722, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21882 (p : Pattern) (guard : d5503 p = 1) : d2723 p ≤ (0 : Int) + d2352 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2723, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21881 p hg
    simpa only [d2723, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2723, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d2723, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21883 (p : Pattern) (guard : d5503 p = 1) : d2724 p ≤ (0 : Int) + d2353 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2724, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21882 p hg
    simpa only [d2724, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2724, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21838 p hg
    simpa only [d2724, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21884 (p : Pattern) (guard : d0 p = 1) : d2702 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21885 (p : Pattern) (guard : d5503 p = 1) : d2702 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21884 p hg
    simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21886 (p : Pattern) (guard : d5503 p = 1) : d2725 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21885 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21864 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21887 (p : Pattern) (guard : d0 p = 1) : d2726 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21888 (p : Pattern) (guard : d5503 p = 1) : d2727 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2727, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5503, d2727, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2727, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21887 p hg
    simpa only [d5503, d2727, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21889 (p : Pattern) (guard : d5503 p = 1) : d2728 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2728, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21888 p hg
    simpa only [d2728, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2728, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2728, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21890 (p : Pattern) (guard : d5503 p = 1) : d2729 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2729, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21886 p hg
    simpa only [d2729, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2729, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21889 p hg
    simpa only [d2729, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21891 (p : Pattern) (guard : d5503 p = 1) : d2730 p ≤ (0 : Int) + d2355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2730, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21883 p hg
    simpa only [d2730, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2730, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21890 p hg
    simpa only [d2730, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21892 (p : Pattern) (guard : d5503 p = 1) : d2731 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2731, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21857 p hg
    simpa only [d2731, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2731, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d2731, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21893 (p : Pattern) (guard : d5503 p = 1) : d2732 p ≤ (0 : Int) + d2357 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2732, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21891 p hg
    simpa only [d2732, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2732, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21892 p hg
    simpa only [d2732, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21894 (p : Pattern) (guard : d5503 p = 1) : d2733 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2733, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21857 p hg
    simpa only [d2733, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2733, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2733, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21895 (p : Pattern) (guard : d5503 p = 1) : d2734 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2734, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21894 p hg
    simpa only [d2734, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2734, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2734, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21896 (p : Pattern) (guard : d5503 p = 1) : d2735 p ≤ (0 : Int) + d2360 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2735, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21893 p hg
    simpa only [d2735, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2735, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21895 p hg
    simpa only [d2735, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21897 (p : Pattern) (guard : d5503 p = 1) : d2736 p ≤ (0 : Int) + d2361 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2736, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21886 p hg
    simpa only [d2736, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2736, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2736, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21898 (p : Pattern) (guard : d5503 p = 1) : d2737 p ≤ (0 : Int) + d2362 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2737, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21870 p hg
    simpa only [d2737, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2737, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21897 p hg
    simpa only [d2737, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21899 (p : Pattern) (guard : d5503 p = 1) : d2738 p ≤ (0 : Int) + d2363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2738, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d2738, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2738, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21737 p hg
    simpa only [d2738, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21900 (p : Pattern) (guard : d5503 p = 1) : d2739 p ≤ (0 : Int) + d2364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2739, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21898 p hg
    simpa only [d2739, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2739, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21899 p hg
    simpa only [d2739, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21901 (p : Pattern) (guard : d5503 p = 1) : d2740 p ≤ (0 : Int) + d2365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2740, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d2740, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2740, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21739 p hg
    simpa only [d2740, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21902 (p : Pattern) (guard : d5503 p = 1) : d2741 p ≤ (0 : Int) + d2366 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2741, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21901 p hg
    simpa only [d2741, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2741, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2741, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21903 (p : Pattern) (guard : d5503 p = 1) : d2742 p ≤ (0 : Int) + d2367 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2742, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21900 p hg
    simpa only [d2742, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2742, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21902 p hg
    simpa only [d2742, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21904 (p : Pattern) (guard : d5503 p = 1) : d2743 p ≤ (0 : Int) + d2368 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2743, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21896 p hg
    simpa only [d2743, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2743, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21903 p hg
    simpa only [d2743, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21905 (p : Pattern) (guard : d5503 p = 1) : d2744 p ≤ (0 : Int) + d2369 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2744, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21879 p hg
    simpa only [d2744, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2744, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21904 p hg
    simpa only [d2744, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21906 (p : Pattern) (guard : d5503 p = 1) : d2745 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2745, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21834 p hg
    simpa only [d2745, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2745, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2745, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21907 (p : Pattern) (guard : d5503 p = 1) : d2746 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21847 p hg
    simpa only [d2746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21906 p hg
    simpa only [d2746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21908 (p : Pattern) (guard : d5503 p = 1) : d2747 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2747, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21852 p hg
    simpa only [d2747, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2747, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2747, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21909 (p : Pattern) (guard : d5503 p = 1) : d2748 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2748, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21853 p hg
    simpa only [d2748, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2748, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21908 p hg
    simpa only [d2748, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21910 (p : Pattern) (guard : d5503 p = 1) : d2749 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2749, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2749, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2749, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d2749, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21911 (p : Pattern) (guard : d5503 p = 1) : d2750 p ≤ (0 : Int) + d2370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2750, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2750, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2750, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21910 p hg
    simpa only [d2750, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21912 (p : Pattern) (guard : d5503 p = 1) : d2751 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2751, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21910 p hg
    simpa only [d2751, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2751, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21860 p hg
    simpa only [d2751, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21913 (p : Pattern) (guard : d5503 p = 1) : d2752 p ≤ (0 : Int) + d2371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2752, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21911 p hg
    simpa only [d2752, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2752, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21912 p hg
    simpa only [d2752, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21914 (p : Pattern) (guard : d5503 p = 1) : d2753 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2753, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21886 p hg
    simpa only [d2753, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2753, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21865 p hg
    simpa only [d2753, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21915 (p : Pattern) (guard : d0 p = 1) : d2707 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21916 (p : Pattern) (guard : d5503 p = 1) : d2707 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21915 p hg
    simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21917 (p : Pattern) (guard : d5503 p = 1) : d2754 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21916 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21868 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21918 (p : Pattern) (guard : d5503 p = 1) : d2755 p ≤ (0 : Int) + d2372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2755, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21917 p hg
    simpa only [d2755, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2755, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21869 p hg
    simpa only [d2755, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21919 (p : Pattern) (guard : d5503 p = 1) : d2756 p ≤ (0 : Int) + d2373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2756, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2756, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2756, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21918 p hg
    simpa only [d2756, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21920 (p : Pattern) (guard : d5503 p = 1) : d2757 p ≤ (0 : Int) + d2374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2757, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21919 p hg
    simpa only [d2757, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2757, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2757, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21921 (p : Pattern) (guard : d5503 p = 1) : d2758 p ≤ (0 : Int) + d2375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2758, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21920 p hg
    simpa only [d2758, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2758, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2758, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21922 (p : Pattern) (guard : d5503 p = 1) : d2759 p ≤ (0 : Int) + d2376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2759, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21913 p hg
    simpa only [d2759, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2759, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21921 p hg
    simpa only [d2759, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21923 (p : Pattern) (guard : d5503 p = 1) : d2760 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2760, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2760, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2760, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2760, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21924 (p : Pattern) (guard : d5503 p = 1) : d2761 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2761, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d2761, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2761, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21724 p hg
    simpa only [d2761, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21925 (p : Pattern) (guard : d5503 p = 1) : d2762 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2762, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21923 p hg
    simpa only [d2762, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2762, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21924 p hg
    simpa only [d2762, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21926 (p : Pattern) (guard : d5503 p = 1) : d2763 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2763, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d2763, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2763, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2763, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21927 (p : Pattern) (guard : d5503 p = 1) : d2764 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2764, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21926 p hg
    simpa only [d2764, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2764, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2764, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21928 (p : Pattern) (guard : d5503 p = 1) : d2765 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2765, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21925 p hg
    simpa only [d2765, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2765, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21927 p hg
    simpa only [d2765, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21929 (p : Pattern) (guard : d5503 p = 1) : d2766 p ≤ (0 : Int) + d2380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2766, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21918 p hg
    simpa only [d2766, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2766, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2766, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21930 (p : Pattern) (guard : d5503 p = 1) : d2767 p ≤ (0 : Int) + d2381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2767, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21929 p hg
    simpa only [d2767, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2767, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2767, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21931 (p : Pattern) (guard : d5503 p = 1) : d2768 p ≤ (0 : Int) + d2382 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2768, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21930 p hg
    simpa only [d2768, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2768, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2768, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21932 (p : Pattern) (guard : d5503 p = 1) : d2769 p ≤ (0 : Int) + d2383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2769, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21928 p hg
    simpa only [d2769, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2769, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21931 p hg
    simpa only [d2769, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21933 (p : Pattern) (guard : d5503 p = 1) : d2770 p ≤ (0 : Int) + d2384 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2770, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21922 p hg
    simpa only [d2770, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2770, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21932 p hg
    simpa only [d2770, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21934 (p : Pattern) (guard : d5503 p = 1) : d2771 p ≤ (0 : Int) + d2385 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2771, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21905 p hg
    simpa only [d2771, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2771, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21933 p hg
    simpa only [d2771, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21935 (p : Pattern) (guard : d5503 p = 1) : d2772 p ≤ (0 : Int) + d2386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2772, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21860 p hg
    simpa only [d2772, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2772, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2772, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21936 (p : Pattern) (guard : d5503 p = 1) : d2773 p ≤ (0 : Int) + d2387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2773, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21935 p hg
    simpa only [d2773, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2773, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2773, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21937 (p : Pattern) (guard : d5503 p = 1) : d2774 p ≤ (0 : Int) + d2388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2774, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21936 p hg
    simpa only [d2774, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2774, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2774, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21938 (p : Pattern) (guard : d5503 p = 1) : d2775 p ≤ (0 : Int) + d2389 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2775, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21937 p hg
    simpa only [d2775, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2775, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2775, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21939 (p : Pattern) (guard : d5503 p = 1) : d2776 p ≤ (0 : Int) + d2390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2776, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21933 p hg
    simpa only [d2776, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2776, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21938 p hg
    simpa only [d2776, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21940 (p : Pattern) (guard : d5503 p = 1) : d2777 p ≤ (0 : Int) + d2391 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2777, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21934 p hg
    simpa only [d2777, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2777, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21939 p hg
    simpa only [d2777, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21941 (p : Pattern) (guard : d5503 p = 1) : d2687 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21843 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21848 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21942 (p : Pattern) (guard : d5503 p = 1) : d2778 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2778, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21941 p hg
    simpa only [d2778, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2778, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21858 p hg
    simpa only [d2778, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21943 (p : Pattern) (guard : d5503 p = 1) : d2779 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2779, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21942 p hg
    simpa only [d2779, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2779, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21861 p hg
    simpa only [d2779, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21944 (p : Pattern) (guard : d5503 p = 1) : d2780 p ≤ (0 : Int) + d2395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2780, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21943 p hg
    simpa only [d2780, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2780, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21878 p hg
    simpa only [d2780, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21945 (p : Pattern) (guard : d5503 p = 1) : d2781 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2781, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21848 p hg
    simpa only [d2781, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2781, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21890 p hg
    simpa only [d2781, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21946 (p : Pattern) (guard : d5503 p = 1) : d2782 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2782, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21945 p hg
    simpa only [d2782, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2782, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21892 p hg
    simpa only [d2782, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21947 (p : Pattern) (guard : d5503 p = 1) : d2783 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2783, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21946 p hg
    simpa only [d2783, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2783, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21895 p hg
    simpa only [d2783, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21948 (p : Pattern) (guard : d5503 p = 1) : d2784 p ≤ (0 : Int) + d2396 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2784, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21947 p hg
    simpa only [d2784, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2784, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21903 p hg
    simpa only [d2784, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21949 (p : Pattern) (guard : d5503 p = 1) : d2785 p ≤ (0 : Int) + d2397 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2785, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21944 p hg
    simpa only [d2785, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2785, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21948 p hg
    simpa only [d2785, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21950 (p : Pattern) (guard : d5503 p = 1) : d2786 p ≤ (0 : Int) + d2398 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2786, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21949 p hg
    simpa only [d2786, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2786, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21933 p hg
    simpa only [d2786, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21951 (p : Pattern) (guard : d5503 p = 1) : d2787 p ≤ (0 : Int) + d2399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2787, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21933 p hg
    simpa only [d2787, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2787, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2787, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21952 (p : Pattern) (guard : d5503 p = 1) : d2788 p ≤ (0 : Int) + d2400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2788, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21950 p hg
    simpa only [d2788, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2788, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21951 p hg
    simpa only [d2788, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21953 (p : Pattern) (guard : d5503 p = 1) : d2789 p ≤ (0 : Int) + d2401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2789, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21940 p hg
    simpa only [d2789, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2789, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21952 p hg
    simpa only [d2789, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21954 (p : Pattern) (guard : d5503 p = 1) : d2790 p ≤ (0 : Int) + d2402 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2790, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21805 p hg
    simpa only [d2790, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2790, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21953 p hg
    simpa only [d2790, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21955 (p : Pattern) (guard : d5503 p = 1) : d2791 p ≤ (0 : Int) + d2403 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2791, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21830 p hg
    simpa only [d2791, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2791, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21954 p hg
    simpa only [d2791, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21956 (p : Pattern) (guard : d5503 p = 1) : d2792 p ≤ (0 : Int) + d2404 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2792, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d2792, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2792, d2404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21687 p hg
    simpa only [d2792, d2404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21957 (p : Pattern) (guard : d5503 p = 1) : d2793 p ≤ (0 : Int) + d2405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2793, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21756 p hg
    simpa only [d2793, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2793, d2405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21956 p hg
    simpa only [d2793, d2405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21958 (p : Pattern) (guard : d5503 p = 1) : d2794 p ≤ (0 : Int) + d2406 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2794, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21710 p hg
    simpa only [d2794, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2794, d2406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21692 p hg
    simpa only [d2794, d2406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21959 (p : Pattern) (guard : d5503 p = 1) : d2795 p ≤ (0 : Int) + d2407 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2795, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21759 p hg
    simpa only [d2795, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2795, d2407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2795, d2407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21960 (p : Pattern) (guard : d5503 p = 1) : d2796 p ≤ (0 : Int) + d2408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2796, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21958 p hg
    simpa only [d2796, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2796, d2408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21959 p hg
    simpa only [d2796, d2408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21961 (p : Pattern) (guard : d5503 p = 1) : d2797 p ≤ (0 : Int) + d2409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2797, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21957 p hg
    simpa only [d2797, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2797, d2409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21960 p hg
    simpa only [d2797, d2409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21962 (p : Pattern) (guard : d5503 p = 1) : d2798 p ≤ (0 : Int) + d2410 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2798, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21733 p hg
    simpa only [d2798, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2798, d2410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21959 p hg
    simpa only [d2798, d2410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21963 (p : Pattern) (guard : d5503 p = 1) : d2799 p ≤ (0 : Int) + d2411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2799, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21962 p hg
    simpa only [d2799, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2799, d2411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21740 p hg
    simpa only [d2799, d2411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21964 (p : Pattern) (guard : d5503 p = 1) : d2800 p ≤ (0 : Int) + d2412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2800, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21961 p hg
    simpa only [d2800, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2800, d2412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21963 p hg
    simpa only [d2800, d2412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21965 (p : Pattern) (guard : d5503 p = 1) : d2801 p ≤ (0 : Int) + d2413 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2801, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21780 p hg
    simpa only [d2801, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2801, d2413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21964 p hg
    simpa only [d2801, d2413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21966 (p : Pattern) (guard : d5503 p = 1) : d2802 p ≤ (0 : Int) + d2414 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2802, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21956 p hg
    simpa only [d2802, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2802, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d2802, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21967 (p : Pattern) (guard : d5503 p = 1) : d2803 p ≤ (0 : Int) + d2415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2803, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21959 p hg
    simpa only [d2803, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2803, d2415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21739 p hg
    simpa only [d2803, d2415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21968 (p : Pattern) (guard : d5503 p = 1) : d2804 p ≤ (0 : Int) + d2416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2804, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21966 p hg
    simpa only [d2804, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2804, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21967 p hg
    simpa only [d2804, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21969 (p : Pattern) (guard : d5503 p = 1) : d2805 p ≤ (0 : Int) + d2417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2805, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21959 p hg
    simpa only [d2805, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2805, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2805, d2417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21970 (p : Pattern) (guard : d5503 p = 1) : d2806 p ≤ (0 : Int) + d2418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2806, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21969 p hg
    simpa only [d2806, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2806, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2806, d2418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21971 (p : Pattern) (guard : d5503 p = 1) : d2807 p ≤ (0 : Int) + d2419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2807, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21968 p hg
    simpa only [d2807, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2807, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21970 p hg
    simpa only [d2807, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21972 (p : Pattern) (guard : d5503 p = 1) : d2808 p ≤ (0 : Int) + d2420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2808, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21770 p hg
    simpa only [d2808, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2808, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21971 p hg
    simpa only [d2808, d2420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21973 (p : Pattern) (guard : d5503 p = 1) : d2809 p ≤ (0 : Int) + d2421 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2809, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21965 p hg
    simpa only [d2809, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2809, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21972 p hg
    simpa only [d2809, d2421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21974 (p : Pattern) (guard : d5503 p = 1) : d2810 p ≤ (0 : Int) + d2422 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2810, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21746 p hg
    simpa only [d2810, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2810, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21761 p hg
    simpa only [d2810, d2422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21975 (p : Pattern) (guard : d5503 p = 1) : d2811 p ≤ (0 : Int) + d2423 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2811, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21974 p hg
    simpa only [d2811, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2811, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21762 p hg
    simpa only [d2811, d2423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21976 (p : Pattern) (guard : d0 p = 1) : d2812 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21977 (p : Pattern) (guard : d5503 p = 1) : d2812 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21976 p hg
    simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21978 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21979 (p : Pattern) (guard : d5503 p = 1) : d2813 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2813, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d5503, d2813, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2813, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21978 p hg
    simpa only [d5503, d2813, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
