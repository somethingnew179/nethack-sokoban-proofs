/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19180 (p : Pattern) (guard : d5503 p = 1) : d2326 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2326, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19175 p hg
    simpa only [d2326, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2326, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19179 p hg
    simpa only [d2326, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19181 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19182 (p : Pattern) (guard : d5503 p = 1) : d2319 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19181 p hg
    simpa only [d5503, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19183 (p : Pattern) (guard : d5503 p = 1) : d2319 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19182 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19184 (p : Pattern) (guard : d5503 p = 1) : d2327 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2327, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d2327, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2327, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19174 p hg
    simpa only [d2327, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19185 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2689 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19186 (p : Pattern) (guard : d5503 p = 1) : d2328 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19185 p hg
    simpa only [d5503, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19187 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2690 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19188 (p : Pattern) (guard : d5503 p = 1) : d2328 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2328, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, d2328, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2328, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19187 p hg
    simpa only [d5503, d2328, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19189 (p : Pattern) (guard : d5503 p = 1) : d2328 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19186 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19188 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19190 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2693 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19191 (p : Pattern) (guard : d5503 p = 1) : d2328 p ≤ (0 : Int) + d2694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2328, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, d2328, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2328, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19190 p hg
    simpa only [d5503, d2328, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19192 (p : Pattern) (guard : d5503 p = 1) : d2329 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2329, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19191 p hg
    simpa only [d2329, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2329, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2329, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19193 (p : Pattern) (guard : d5503 p = 1) : d2330 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2330, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19189 p hg
    simpa only [d2330, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2330, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19192 p hg
    simpa only [d2330, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19194 (p : Pattern) (guard : d5503 p = 1) : d2331 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2331, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19184 p hg
    simpa only [d2331, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2331, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19193 p hg
    simpa only [d2331, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19195 (p : Pattern) (guard : d5503 p = 1) : d2332 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2332, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19180 p hg
    simpa only [d2332, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2332, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19194 p hg
    simpa only [d2332, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19196 (p : Pattern) (guard : d5503 p = 1) : d2333 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2333, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d2333, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2333, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2333, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19197 (p : Pattern) (guard : d5503 p = 1) : d2334 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2334, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19194 p hg
    simpa only [d2334, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2334, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19196 p hg
    simpa only [d2334, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19198 (p : Pattern) (guard : d5503 p = 1) : d2335 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2335, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19195 p hg
    simpa only [d2335, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2335, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19197 p hg
    simpa only [d2335, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19199 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2703 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19200 (p : Pattern) (guard : d5503 p = 1) : d2336 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, d2336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19199 p hg
    simpa only [d5503, d2336, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19201 (p : Pattern) (guard : d5503 p = 1) : d2337 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2337, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19200 p hg
    simpa only [d2337, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2337, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2337, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19202 (p : Pattern) (guard : d5503 p = 1) : d2338 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2338, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d2338, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2338, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19201 p hg
    simpa only [d2338, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19203 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19204 (p : Pattern) (guard : d5503 p = 1) : d2339 p ≤ (0 : Int) + d2709 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2339, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d5503, d2339, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2339, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19203 p hg
    simpa only [d5503, d2339, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19205 (p : Pattern) (guard : d5503 p = 1) : d2340 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2340, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19204 p hg
    simpa only [d2340, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2340, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2340, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19206 (p : Pattern) (guard : d5503 p = 1) : d2341 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2341, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d2341, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2341, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19205 p hg
    simpa only [d2341, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19207 (p : Pattern) (guard : d5503 p = 1) : d2342 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2342, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19202 p hg
    simpa only [d2342, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2342, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19206 p hg
    simpa only [d2342, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19208 (p : Pattern) (guard : d5503 p = 1) : d2343 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2343, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d2343, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2343, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2343, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19209 (p : Pattern) (guard : d5503 p = 1) : d2344 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2344, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19189 p hg
    simpa only [d2344, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2344, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2344, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19210 (p : Pattern) (guard : d5503 p = 1) : d2345 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2345, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19208 p hg
    simpa only [d2345, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2345, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d2345, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19211 (p : Pattern) (guard : d5503 p = 1) : d2346 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2346, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19207 p hg
    simpa only [d2346, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2346, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19210 p hg
    simpa only [d2346, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19212 (p : Pattern) (guard : d5503 p = 1) : d2347 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2347, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19073 p hg
    simpa only [d2347, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2347, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2347, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19213 (p : Pattern) (guard : d5503 p = 1) : d2348 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2348, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19210 p hg
    simpa only [d2348, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2348, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19212 p hg
    simpa only [d2348, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19214 (p : Pattern) (guard : d5503 p = 1) : d2349 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2349, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19211 p hg
    simpa only [d2349, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2349, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19213 p hg
    simpa only [d2349, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19215 (p : Pattern) (guard : d5503 p = 1) : d2350 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2350, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19198 p hg
    simpa only [d2350, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2350, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19214 p hg
    simpa only [d2350, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19216 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d2677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19217 (p : Pattern) (guard : d5503 p = 1) : d2351 p ≤ (0 : Int) + d2722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2351, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15077 p hg
    simpa only [d5503, d2351, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2351, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19216 p hg
    simpa only [d5503, d2351, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19218 (p : Pattern) (guard : d5503 p = 1) : d2352 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2352, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19217 p hg
    simpa only [d2352, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2352, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d2352, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19219 (p : Pattern) (guard : d5503 p = 1) : d2353 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2353, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19218 p hg
    simpa only [d2353, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2353, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19174 p hg
    simpa only [d2353, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19220 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19221 (p : Pattern) (guard : d5503 p = 1) : d2336 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19220 p hg
    simpa only [d5503, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19222 (p : Pattern) (guard : d5503 p = 1) : d2336 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19221 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19200 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19223 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2726 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19224 (p : Pattern) (guard : d5503 p = 1) : d2336 p ≤ (0 : Int) + d2727 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2336, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, d2336, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2336, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19223 p hg
    simpa only [d5503, d2336, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19225 (p : Pattern) (guard : d5503 p = 1) : d2337 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2337, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19224 p hg
    simpa only [d2337, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2337, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2337, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19226 (p : Pattern) (guard : d5503 p = 1) : d2354 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2354, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19222 p hg
    simpa only [d2354, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2354, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19225 p hg
    simpa only [d2354, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19227 (p : Pattern) (guard : d5503 p = 1) : d2355 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2355, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19219 p hg
    simpa only [d2355, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2355, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19226 p hg
    simpa only [d2355, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19228 (p : Pattern) (guard : d5503 p = 1) : d2356 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2356, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19193 p hg
    simpa only [d2356, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2356, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d2356, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19229 (p : Pattern) (guard : d5503 p = 1) : d2357 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2357, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19227 p hg
    simpa only [d2357, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2357, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19228 p hg
    simpa only [d2357, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19230 (p : Pattern) (guard : d5503 p = 1) : d2358 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2358, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19193 p hg
    simpa only [d2358, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2358, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2358, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19231 (p : Pattern) (guard : d5503 p = 1) : d2359 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2359, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19230 p hg
    simpa only [d2359, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2359, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2359, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19232 (p : Pattern) (guard : d5503 p = 1) : d2360 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2360, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19229 p hg
    simpa only [d2360, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2360, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19231 p hg
    simpa only [d2360, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19233 (p : Pattern) (guard : d5503 p = 1) : d2361 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2361, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19222 p hg
    simpa only [d2361, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2361, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2361, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19234 (p : Pattern) (guard : d5503 p = 1) : d2362 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2362, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19206 p hg
    simpa only [d2362, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2362, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19233 p hg
    simpa only [d2362, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19235 (p : Pattern) (guard : d5503 p = 1) : d2363 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2363, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d2363, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2363, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19073 p hg
    simpa only [d2363, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19236 (p : Pattern) (guard : d5503 p = 1) : d2364 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2364, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19234 p hg
    simpa only [d2364, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2364, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19235 p hg
    simpa only [d2364, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19237 (p : Pattern) (guard : d5503 p = 1) : d2365 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2365, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d2365, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2365, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19075 p hg
    simpa only [d2365, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19238 (p : Pattern) (guard : d5503 p = 1) : d2366 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2366, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19237 p hg
    simpa only [d2366, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2366, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2366, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19239 (p : Pattern) (guard : d5503 p = 1) : d2367 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2367, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19236 p hg
    simpa only [d2367, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2367, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19238 p hg
    simpa only [d2367, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19240 (p : Pattern) (guard : d5503 p = 1) : d2368 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2368, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19232 p hg
    simpa only [d2368, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2368, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19239 p hg
    simpa only [d2368, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19241 (p : Pattern) (guard : d5503 p = 1) : d2369 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2369, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19215 p hg
    simpa only [d2369, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2369, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19240 p hg
    simpa only [d2369, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19242 (p : Pattern) (guard : d5503 p = 1) : d2321 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2321, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d2321, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2321, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2321, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19243 (p : Pattern) (guard : d5503 p = 1) : d2327 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2327, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d2327, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2327, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19242 p hg
    simpa only [d2327, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19244 (p : Pattern) (guard : d5503 p = 1) : d2329 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2329, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19188 p hg
    simpa only [d2329, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2329, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2329, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19245 (p : Pattern) (guard : d5503 p = 1) : d2330 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2330, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19189 p hg
    simpa only [d2330, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2330, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19244 p hg
    simpa only [d2330, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19246 (p : Pattern) (guard : d5503 p = 1) : d2331 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2331, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2331, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2331, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d2331, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19247 (p : Pattern) (guard : d5503 p = 1) : d2370 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2370, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2370, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2370, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19246 p hg
    simpa only [d2370, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19248 (p : Pattern) (guard : d5503 p = 1) : d2334 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2334, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19246 p hg
    simpa only [d2334, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2334, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19196 p hg
    simpa only [d2334, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19249 (p : Pattern) (guard : d5503 p = 1) : d2371 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2371, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19247 p hg
    simpa only [d2371, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2371, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19248 p hg
    simpa only [d2371, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19250 (p : Pattern) (guard : d5503 p = 1) : d2354 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2354, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19222 p hg
    simpa only [d2354, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2354, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19201 p hg
    simpa only [d2354, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19251 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19252 (p : Pattern) (guard : d5503 p = 1) : d2339 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19251 p hg
    simpa only [d5503, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19253 (p : Pattern) (guard : d5503 p = 1) : d2339 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19252 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19204 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19254 (p : Pattern) (guard : d5503 p = 1) : d2372 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2372, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19253 p hg
    simpa only [d2372, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2372, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19205 p hg
    simpa only [d2372, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19255 (p : Pattern) (guard : d5503 p = 1) : d2373 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2373, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2373, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2373, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19254 p hg
    simpa only [d2373, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19256 (p : Pattern) (guard : d5503 p = 1) : d2374 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2374, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19255 p hg
    simpa only [d2374, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2374, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2374, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19257 (p : Pattern) (guard : d5503 p = 1) : d2375 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2375, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19256 p hg
    simpa only [d2375, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2375, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2375, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19258 (p : Pattern) (guard : d5503 p = 1) : d2376 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2376, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19249 p hg
    simpa only [d2376, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2376, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19257 p hg
    simpa only [d2376, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19259 (p : Pattern) (guard : d5503 p = 1) : d2377 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2377, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2377, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2377, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2377, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19260 (p : Pattern) (guard : d5503 p = 1) : d2356 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2356, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d2356, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2356, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d2356, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19261 (p : Pattern) (guard : d5503 p = 1) : d2378 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2378, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19259 p hg
    simpa only [d2378, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2378, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19260 p hg
    simpa only [d2378, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19262 (p : Pattern) (guard : d5503 p = 1) : d2358 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2358, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d2358, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2358, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2358, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19263 (p : Pattern) (guard : d5503 p = 1) : d2359 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2359, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19262 p hg
    simpa only [d2359, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2359, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2359, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19264 (p : Pattern) (guard : d5503 p = 1) : d2379 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2379, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19261 p hg
    simpa only [d2379, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2379, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19263 p hg
    simpa only [d2379, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19265 (p : Pattern) (guard : d5503 p = 1) : d2380 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2380, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19254 p hg
    simpa only [d2380, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2380, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2380, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19266 (p : Pattern) (guard : d5503 p = 1) : d2381 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2381, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19265 p hg
    simpa only [d2381, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2381, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2381, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19267 (p : Pattern) (guard : d5503 p = 1) : d2382 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2382, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19266 p hg
    simpa only [d2382, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2382, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2382, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19268 (p : Pattern) (guard : d5503 p = 1) : d2383 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2383, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19264 p hg
    simpa only [d2383, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2383, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19267 p hg
    simpa only [d2383, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19269 (p : Pattern) (guard : d5503 p = 1) : d2384 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2384, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19258 p hg
    simpa only [d2384, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2384, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19268 p hg
    simpa only [d2384, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19270 (p : Pattern) (guard : d5503 p = 1) : d2385 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2385, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19241 p hg
    simpa only [d2385, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2385, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19269 p hg
    simpa only [d2385, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19271 (p : Pattern) (guard : d5503 p = 1) : d2386 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2386, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19196 p hg
    simpa only [d2386, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2386, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2386, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19272 (p : Pattern) (guard : d5503 p = 1) : d2387 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2387, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19271 p hg
    simpa only [d2387, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2387, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2387, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19273 (p : Pattern) (guard : d5503 p = 1) : d2388 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2388, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19272 p hg
    simpa only [d2388, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2388, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2388, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19274 (p : Pattern) (guard : d5503 p = 1) : d2389 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2389, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19273 p hg
    simpa only [d2389, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2389, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2389, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19275 (p : Pattern) (guard : d5503 p = 1) : d2390 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2390, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19269 p hg
    simpa only [d2390, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2390, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19274 p hg
    simpa only [d2390, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19276 (p : Pattern) (guard : d5503 p = 1) : d2391 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2391, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19270 p hg
    simpa only [d2391, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2391, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19275 p hg
    simpa only [d2391, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19277 (p : Pattern) (guard : d5503 p = 1) : d2392 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19179 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19184 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19278 (p : Pattern) (guard : d5503 p = 1) : d2393 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2393, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19277 p hg
    simpa only [d2393, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2393, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19194 p hg
    simpa only [d2393, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19279 (p : Pattern) (guard : d5503 p = 1) : d2394 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2394, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19278 p hg
    simpa only [d2394, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2394, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19197 p hg
    simpa only [d2394, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19280 (p : Pattern) (guard : d5503 p = 1) : d2395 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2395, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19279 p hg
    simpa only [d2395, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2395, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19214 p hg
    simpa only [d2395, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19281 (p : Pattern) (guard : d5503 p = 1) : d2377 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2377, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19184 p hg
    simpa only [d2377, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2377, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19226 p hg
    simpa only [d2377, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19282 (p : Pattern) (guard : d5503 p = 1) : d2378 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2378, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19281 p hg
    simpa only [d2378, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2378, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19228 p hg
    simpa only [d2378, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19283 (p : Pattern) (guard : d5503 p = 1) : d2379 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2379, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19282 p hg
    simpa only [d2379, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2379, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19231 p hg
    simpa only [d2379, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19284 (p : Pattern) (guard : d5503 p = 1) : d2396 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2396, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19283 p hg
    simpa only [d2396, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2396, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19239 p hg
    simpa only [d2396, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19285 (p : Pattern) (guard : d5503 p = 1) : d2397 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2397, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19280 p hg
    simpa only [d2397, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2397, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19284 p hg
    simpa only [d2397, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19286 (p : Pattern) (guard : d5503 p = 1) : d2398 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2398, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19285 p hg
    simpa only [d2398, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2398, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19269 p hg
    simpa only [d2398, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19287 (p : Pattern) (guard : d5503 p = 1) : d2399 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2399, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19269 p hg
    simpa only [d2399, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2399, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2399, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19288 (p : Pattern) (guard : d5503 p = 1) : d2400 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2400, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19286 p hg
    simpa only [d2400, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2400, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19287 p hg
    simpa only [d2400, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19289 (p : Pattern) (guard : d5503 p = 1) : d2401 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2401, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19276 p hg
    simpa only [d2401, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2401, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19288 p hg
    simpa only [d2401, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19290 (p : Pattern) (guard : d5503 p = 1) : d2402 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2402, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19141 p hg
    simpa only [d2402, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2402, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19289 p hg
    simpa only [d2402, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19291 (p : Pattern) (guard : d5503 p = 1) : d2403 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2403, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19166 p hg
    simpa only [d2403, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2403, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19290 p hg
    simpa only [d2403, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19292 (p : Pattern) (guard : d5503 p = 1) : d2404 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2404, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d2404, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2404, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d2404, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19293 (p : Pattern) (guard : d5503 p = 1) : d2405 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2405, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19092 p hg
    simpa only [d2405, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2405, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19292 p hg
    simpa only [d2405, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19294 (p : Pattern) (guard : d5503 p = 1) : d2406 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2406, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d2406, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2406, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19028 p hg
    simpa only [d2406, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19295 (p : Pattern) (guard : d5503 p = 1) : d2407 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2407, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19095 p hg
    simpa only [d2407, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2407, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2407, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19296 (p : Pattern) (guard : d5503 p = 1) : d2408 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2408, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19294 p hg
    simpa only [d2408, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2408, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d2408, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19297 (p : Pattern) (guard : d5503 p = 1) : d2409 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2409, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19293 p hg
    simpa only [d2409, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2409, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19296 p hg
    simpa only [d2409, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19298 (p : Pattern) (guard : d5503 p = 1) : d2410 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2410, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19069 p hg
    simpa only [d2410, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2410, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d2410, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19299 (p : Pattern) (guard : d5503 p = 1) : d2411 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2411, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19298 p hg
    simpa only [d2411, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2411, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19076 p hg
    simpa only [d2411, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19300 (p : Pattern) (guard : d5503 p = 1) : d2412 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2412, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19297 p hg
    simpa only [d2412, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2412, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19299 p hg
    simpa only [d2412, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19301 (p : Pattern) (guard : d5503 p = 1) : d2413 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2413, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19116 p hg
    simpa only [d2413, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2413, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19300 p hg
    simpa only [d2413, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19302 (p : Pattern) (guard : d5503 p = 1) : d2414 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2414, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19292 p hg
    simpa only [d2414, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2414, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d2414, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19303 (p : Pattern) (guard : d5503 p = 1) : d2415 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2415, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d2415, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2415, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19075 p hg
    simpa only [d2415, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19304 (p : Pattern) (guard : d5503 p = 1) : d2416 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2416, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19302 p hg
    simpa only [d2416, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2416, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19303 p hg
    simpa only [d2416, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19305 (p : Pattern) (guard : d5503 p = 1) : d2417 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2417, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d2417, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2417, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2417, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19306 (p : Pattern) (guard : d5503 p = 1) : d2418 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2418, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19305 p hg
    simpa only [d2418, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2418, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2418, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19307 (p : Pattern) (guard : d5503 p = 1) : d2419 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2419, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19304 p hg
    simpa only [d2419, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2419, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19306 p hg
    simpa only [d2419, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19308 (p : Pattern) (guard : d5503 p = 1) : d2420 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2420, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19106 p hg
    simpa only [d2420, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2420, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19307 p hg
    simpa only [d2420, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19309 (p : Pattern) (guard : d5503 p = 1) : d2421 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2421, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19301 p hg
    simpa only [d2421, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2421, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19308 p hg
    simpa only [d2421, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19310 (p : Pattern) (guard : d5503 p = 1) : d2422 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2422, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d2422, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2422, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19097 p hg
    simpa only [d2422, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19311 (p : Pattern) (guard : d5503 p = 1) : d2423 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2423, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19310 p hg
    simpa only [d2423, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2423, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19098 p hg
    simpa only [d2423, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19312 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2812 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19313 (p : Pattern) (guard : d5503 p = 1) : d2424 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19312 p hg
    simpa only [d5503, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19314 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19315 (p : Pattern) (guard : d5503 p = 1) : d2424 p ≤ (0 : Int) + d2813 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2424, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d5503, d2424, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2424, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19314 p hg
    simpa only [d5503, d2424, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19316 (p : Pattern) (guard : d5503 p = 1) : d2424 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19313 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19315 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19317 (p : Pattern) (guard : d5503 p = 1) : d2425 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2425, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19315 p hg
    simpa only [d2425, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2425, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2425, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19318 (p : Pattern) (guard : d5503 p = 1) : d2426 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2426, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19316 p hg
    simpa only [d2426, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2426, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19317 p hg
    simpa only [d2426, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19319 (p : Pattern) (guard : d5503 p = 1) : d2427 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2427, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d2427, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2427, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19318 p hg
    simpa only [d2427, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
