/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons294
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41300 (p : Pattern) (guard : d8136 p = 1) : d2457 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2457, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41289 p hg
    simpa only [d8136, d2457, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2457, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41299 p hg
    simpa only [d8136, d2457, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41301 (p : Pattern) (guard : d8137 p = 1) : d2458 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2458, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41281 p hg
    simpa only [d8137, d2458, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2458, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41300 p hg
    simpa only [d8137, d2458, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41302 (p : Pattern) (guard : d8112 p = 1) : d2327 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41234 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41303 (p : Pattern) (guard : d8117 p = 1) : d2331 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41282 p hg
    simpa only [d8117, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40851 p hg
    simpa only [d8117, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41304 (p : Pattern) (guard : d8118 p = 1) : d2370 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41302 p hg
    simpa only [d8118, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41303 p hg
    simpa only [d8118, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41305 (p : Pattern) (guard : d8123 p = 1) : d2334 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41284 p hg
    simpa only [d8123, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40854 p hg
    simpa only [d8123, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41306 (p : Pattern) (guard : d8124 p = 1) : d2371 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41304 p hg
    simpa only [d8124, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41305 p hg
    simpa only [d8124, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41307 (p : Pattern) (guard : d8117 p = 1) : d2373 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40760 p hg
    simpa only [d8117, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40858 p hg
    simpa only [d8117, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41308 (p : Pattern) (guard : d8123 p = 1) : d2374 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41307 p hg
    simpa only [d8123, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41309 (p : Pattern) (guard : d8129 p = 1) : d2375 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41308 p hg
    simpa only [d8129, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41310 (p : Pattern) (guard : d8130 p = 1) : d2376 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41306 p hg
    simpa only [d8130, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41309 p hg
    simpa only [d8130, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41311 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35817 p hg
    simpa only [d8099, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41312 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41311 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41313 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41312 p hg
    simpa only [d8111, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41314 (p : Pattern) (guard : d0 p = 1) : d2354 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41315 (p : Pattern) (guard : d8117 p = 1) : d2377 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41313 p hg
    simpa only [d8117, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41314 p hg
    simpa only [d8117, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41316 (p : Pattern) (guard : d0 p = 1) : d2444 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41317 (p : Pattern) (guard : d8123 p = 1) : d2454 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2454, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41315 p hg
    simpa only [d8123, d2454, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2454, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41316 p hg
    simpa only [d8123, d2454, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41318 (p : Pattern) (guard : d8129 p = 1) : d2455 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2455, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41317 p hg
    simpa only [d8129, d2455, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2455, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41297 p hg
    simpa only [d8129, d2455, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41319 (p : Pattern) (guard : d8135 p = 1) : d2456 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2456, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41318 p hg
    simpa only [d8135, d2456, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2456, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d8135, d2456, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41320 (p : Pattern) (guard : d8136 p = 1) : d2457 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2457, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41310 p hg
    simpa only [d8136, d2457, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2457, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41319 p hg
    simpa only [d8136, d2457, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41321 (p : Pattern) (guard : d8123 p = 1) : d2386 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41244 p hg
    simpa only [d8123, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41322 (p : Pattern) (guard : d8129 p = 1) : d2387 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41321 p hg
    simpa only [d8129, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41323 (p : Pattern) (guard : d8135 p = 1) : d2388 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41322 p hg
    simpa only [d8135, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41324 (p : Pattern) (guard : d8141 p = 1) : d2389 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41323 p hg
    simpa only [d8141, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41325 (p : Pattern) (guard : d8142 p = 1) : d2459 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2459, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41320 p hg
    simpa only [d8142, d2459, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2459, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41324 p hg
    simpa only [d8142, d2459, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41326 (p : Pattern) (guard : d8143 p = 1) : d2460 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2460, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41301 p hg
    simpa only [d8143, d2460, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2460, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41325 p hg
    simpa only [d8143, d2460, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41327 (p : Pattern) (guard : d8112 p = 1) : d2392 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41230 p hg
    simpa only [d8112, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41313 p hg
    simpa only [d8112, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41328 (p : Pattern) (guard : d0 p = 1) : d2330 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41329 (p : Pattern) (guard : d8117 p = 1) : d2331 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d8117, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41328 p hg
    simpa only [d8117, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41330 (p : Pattern) (guard : d8118 p = 1) : d2393 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41327 p hg
    simpa only [d8118, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41329 p hg
    simpa only [d8118, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41331 (p : Pattern) (guard : d8123 p = 1) : d2334 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41303 p hg
    simpa only [d8123, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40854 p hg
    simpa only [d8123, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41332 (p : Pattern) (guard : d8124 p = 1) : d2394 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41330 p hg
    simpa only [d8124, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41331 p hg
    simpa only [d8124, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41333 (p : Pattern) (guard : d0 p = 1) : d2461 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41334 (p : Pattern) (guard : d8117 p = 1) : d2462 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2462, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40791 p hg
    simpa only [d8117, d2462, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2462, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41333 p hg
    simpa only [d8117, d2462, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41335 (p : Pattern) (guard : d8123 p = 1) : d2463 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2463, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41334 p hg
    simpa only [d8123, d2463, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2463, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41276 p hg
    simpa only [d8123, d2463, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41336 (p : Pattern) (guard : d0 p = 1) : d2466 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41337 (p : Pattern) (guard : d8129 p = 1) : d2467 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2467, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41335 p hg
    simpa only [d8129, d2467, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2467, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41336 p hg
    simpa only [d8129, d2467, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41338 (p : Pattern) (guard : d8130 p = 1) : d2468 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2468, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41332 p hg
    simpa only [d8130, d2468, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2468, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41337 p hg
    simpa only [d8130, d2468, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41339 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35835 p hg
    simpa only [d8099, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41340 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41339 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41341 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41340 p hg
    simpa only [d8111, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41342 (p : Pattern) (guard : d0 p = 1) : d2354 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41343 (p : Pattern) (guard : d8117 p = 1) : d2377 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41341 p hg
    simpa only [d8117, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41342 p hg
    simpa only [d8117, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41344 (p : Pattern) (guard : d0 p = 1) : d2444 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41345 (p : Pattern) (guard : d8123 p = 1) : d2454 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2454, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41343 p hg
    simpa only [d8123, d2454, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2454, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41344 p hg
    simpa only [d8123, d2454, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41346 (p : Pattern) (guard : d0 p = 1) : d2446 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41347 (p : Pattern) (guard : d8129 p = 1) : d2455 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2455, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41345 p hg
    simpa only [d8129, d2455, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2455, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41346 p hg
    simpa only [d8129, d2455, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41348 (p : Pattern) (guard : d0 p = 1) : d2473 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41349 (p : Pattern) (guard : d8135 p = 1) : d2474 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2474, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41347 p hg
    simpa only [d8135, d2474, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2474, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41348 p hg
    simpa only [d8135, d2474, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41350 (p : Pattern) (guard : d8136 p = 1) : d2475 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2475, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41338 p hg
    simpa only [d8136, d2475, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2475, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41349 p hg
    simpa only [d8136, d2475, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41351 (p : Pattern) (guard : d0 p = 1) : d2327 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41352 (p : Pattern) (guard : d8117 p = 1) : d2327 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41282 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41351 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41353 (p : Pattern) (guard : d0 p = 1) : d2476 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41354 (p : Pattern) (guard : d8123 p = 1) : d2477 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2477, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41352 p hg
    simpa only [d8123, d2477, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2477, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41353 p hg
    simpa only [d8123, d2477, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41355 (p : Pattern) (guard : d8129 p = 1) : d2478 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2478, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41354 p hg
    simpa only [d8129, d2478, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2478, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40870 p hg
    simpa only [d8129, d2478, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41356 (p : Pattern) (guard : d8135 p = 1) : d2479 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2479, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41355 p hg
    simpa only [d8135, d2479, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2479, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d8135, d2479, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41357 (p : Pattern) (guard : d0 p = 1) : d2484 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41358 (p : Pattern) (guard : d8141 p = 1) : d2485 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2485, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41356 p hg
    simpa only [d8141, d2485, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2485, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41357 p hg
    simpa only [d8141, d2485, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41359 (p : Pattern) (guard : d8142 p = 1) : d2486 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2486, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41350 p hg
    simpa only [d8142, d2486, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2486, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41358 p hg
    simpa only [d8142, d2486, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41360 (p : Pattern) (guard : d0 p = 1) : d2327 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41361 (p : Pattern) (guard : d8117 p = 1) : d2327 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41360 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41362 (p : Pattern) (guard : d0 p = 1) : d2487 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41363 (p : Pattern) (guard : d8123 p = 1) : d2488 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2488, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41361 p hg
    simpa only [d8123, d2488, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2488, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41362 p hg
    simpa only [d8123, d2488, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41364 (p : Pattern) (guard : d0 p = 1) : d2490 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41365 (p : Pattern) (guard : d8129 p = 1) : d2491 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2491, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41363 p hg
    simpa only [d8129, d2491, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2491, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41364 p hg
    simpa only [d8129, d2491, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41366 (p : Pattern) (guard : d0 p = 1) : d2494 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41367 (p : Pattern) (guard : d8135 p = 1) : d2495 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2495, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41365 p hg
    simpa only [d8135, d2495, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2495, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41366 p hg
    simpa only [d8135, d2495, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41368 (p : Pattern) (guard : d0 p = 1) : d2484 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41369 (p : Pattern) (guard : d8141 p = 1) : d2496 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d2496, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41367 p hg
    simpa only [d8141, d2496, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d2496, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41368 p hg
    simpa only [d8141, d2496, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41370 (p : Pattern) (guard : d8147 p = 1) : d2497 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d2497, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41369 p hg
    simpa only [d8147, d2497, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d2497, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d2497, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41371 (p : Pattern) (guard : d8148 p = 1) : d2498 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d2498, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41359 p hg
    simpa only [d8148, d2498, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d2498, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41370 p hg
    simpa only [d8148, d2498, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41372 (p : Pattern) (guard : d8149 p = 1) : d2499 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d2499, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41326 p hg
    simpa only [d8149, d2499, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d2499, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41371 p hg
    simpa only [d8149, d2499, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41373 (p : Pattern) (guard : d8150 p = 1) : d2500 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d2500, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d8150, d2500, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d2500, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41372 p hg
    simpa only [d8150, d2500, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41374 (p : Pattern) (guard : d8151 p = 1) : d2501 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41077 p hg
    simpa only [d8151, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41373 p hg
    simpa only [d8151, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41375 (p : Pattern) (guard : d8152 p = 1) : d2502 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40892 p hg
    simpa only [d8152, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41374 p hg
    simpa only [d8152, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41376 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38600 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41377 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41376 p hg
    simpa only [d8101, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41378 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8102, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41377 p hg
    simpa only [d8102, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41379 (p : Pattern) (guard : d8107 p = 1) : d55 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34629 p hg
    simpa only [d8107, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d8107, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41380 (p : Pattern) (guard : d8108 p = 1) : d56 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41378 p hg
    simpa only [d8108, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41379 p hg
    simpa only [d8108, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41381 (p : Pattern) (guard : d8107 p = 1) : d61 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34597 p hg
    simpa only [d8107, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34603 p hg
    simpa only [d8107, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41382 (p : Pattern) (guard : d8113 p = 1) : d64 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41381 p hg
    simpa only [d8113, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41383 (p : Pattern) (guard : d8114 p = 1) : d65 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41380 p hg
    simpa only [d8114, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41382 p hg
    simpa only [d8114, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41384 (p : Pattern) (guard : d8120 p = 1) : d86 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41383 p hg
    simpa only [d8120, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34614 p hg
    simpa only [d8120, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41385 (p : Pattern) (guard : d8121 p = 1) : d87 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38114 p hg
    simpa only [d8121, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41384 p hg
    simpa only [d8121, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41386 (p : Pattern) (guard : d8113 p = 1) : d91 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34515 p hg
    simpa only [d8113, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41387 (p : Pattern) (guard : d8119 p = 1) : d93 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41386 p hg
    simpa only [d8119, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41388 (p : Pattern) (guard : d8125 p = 1) : d95 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41387 p hg
    simpa only [d8125, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41389 (p : Pattern) (guard : d8126 p = 1) : d96 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38122 p hg
    simpa only [d8126, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d8126, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41390 (p : Pattern) (guard : d8127 p = 1) : d97 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41385 p hg
    simpa only [d8127, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41389 p hg
    simpa only [d8127, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41391 (p : Pattern) (guard : d8128 p = 1) : d98 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34617 p hg
    simpa only [d8128, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41390 p hg
    simpa only [d8128, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41392 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8107, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41393 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41392 p hg
    simpa only [d8113, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34725 p hg
    simpa only [d8113, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41394 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41393 p hg
    simpa only [d8119, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34731 p hg
    simpa only [d8119, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41395 (p : Pattern) (guard : d8125 p = 1) : d86 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41394 p hg
    simpa only [d8125, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d8125, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41396 (p : Pattern) (guard : d8126 p = 1) : d87 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38135 p hg
    simpa only [d8126, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41395 p hg
    simpa only [d8126, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41397 (p : Pattern) (guard : d8132 p = 1) : d99 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41396 p hg
    simpa only [d8132, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41398 (p : Pattern) (guard : d8133 p = 1) : d100 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34740 p hg
    simpa only [d8133, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41397 p hg
    simpa only [d8133, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41399 (p : Pattern) (guard : d8134 p = 1) : d101 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41391 p hg
    simpa only [d8134, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41398 p hg
    simpa only [d8134, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41400 (p : Pattern) (guard : d8130 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8130, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41401 (p : Pattern) (guard : d8131 p = 1) : d96 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38153 p hg
    simpa only [d8131, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d8131, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41402 (p : Pattern) (guard : d8132 p = 1) : d97 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35025 p hg
    simpa only [d8132, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41401 p hg
    simpa only [d8132, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41403 (p : Pattern) (guard : d8133 p = 1) : d98 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34841 p hg
    simpa only [d8133, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41402 p hg
    simpa only [d8133, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41404 (p : Pattern) (guard : d8137 p = 1) : d99 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35078 p hg
    simpa only [d8137, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41405 (p : Pattern) (guard : d8138 p = 1) : d100 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34941 p hg
    simpa only [d8138, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41404 p hg
    simpa only [d8138, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41406 (p : Pattern) (guard : d8139 p = 1) : d101 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41403 p hg
    simpa only [d8139, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41405 p hg
    simpa only [d8139, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41407 (p : Pattern) (guard : d8140 p = 1) : d101 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41399 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41406 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41408 (p : Pattern) (guard : d8125 p = 1) : d86 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d8125, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d8125, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41409 (p : Pattern) (guard : d8126 p = 1) : d87 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38175 p hg
    simpa only [d8126, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41408 p hg
    simpa only [d8126, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41410 (p : Pattern) (guard : d8118 p = 1) : d91 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34996 p hg
    simpa only [d8118, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41411 (p : Pattern) (guard : d8124 p = 1) : d93 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41410 p hg
    simpa only [d8124, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41412 (p : Pattern) (guard : d8130 p = 1) : d95 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41411 p hg
    simpa only [d8130, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41413 (p : Pattern) (guard : d8131 p = 1) : d96 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38180 p hg
    simpa only [d8131, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d8131, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41414 (p : Pattern) (guard : d8132 p = 1) : d97 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41409 p hg
    simpa only [d8132, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41413 p hg
    simpa only [d8132, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41415 (p : Pattern) (guard : d8133 p = 1) : d98 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d8133, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41414 p hg
    simpa only [d8133, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41416 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8112, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41417 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41416 p hg
    simpa only [d8118, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d8118, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41418 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41417 p hg
    simpa only [d8124, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d8124, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41419 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41418 p hg
    simpa only [d8130, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41420 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38190 p hg
    simpa only [d8131, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41419 p hg
    simpa only [d8131, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41421 (p : Pattern) (guard : d8137 p = 1) : d99 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41420 p hg
    simpa only [d8137, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41422 (p : Pattern) (guard : d8138 p = 1) : d100 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35079 p hg
    simpa only [d8138, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41421 p hg
    simpa only [d8138, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41423 (p : Pattern) (guard : d8139 p = 1) : d101 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41415 p hg
    simpa only [d8139, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41422 p hg
    simpa only [d8139, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41424 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39302 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41425 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41424 p hg
    simpa only [d8111, d132, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41426 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35302 p hg
    simpa only [d8112, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41425 p hg
    simpa only [d8112, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41427 (p : Pattern) (guard : d8117 p = 1) : d134 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d134, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35309 p hg
    simpa only [d8117, d134, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d134, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d134, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41428 (p : Pattern) (guard : d8118 p = 1) : d135 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d135, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41426 p hg
    simpa only [d8118, d135, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d135, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41427 p hg
    simpa only [d8118, d135, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41429 (p : Pattern) (guard : d8124 p = 1) : d138 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d138, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41428 p hg
    simpa only [d8124, d138, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d138, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35288 p hg
    simpa only [d8124, d138, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41430 (p : Pattern) (guard : d8130 p = 1) : d156 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d156, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41429 p hg
    simpa only [d8130, d156, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d156, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35292 p hg
    simpa only [d8130, d156, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41431 (p : Pattern) (guard : d8131 p = 1) : d157 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d157, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38214 p hg
    simpa only [d8131, d157, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d157, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41430 p hg
    simpa only [d8131, d157, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41432 (p : Pattern) (guard : d8137 p = 1) : d163 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d163, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41431 p hg
    simpa only [d8137, d163, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d163, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d163, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41433 (p : Pattern) (guard : d8138 p = 1) : d164 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d164, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35295 p hg
    simpa only [d8138, d164, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d164, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41432 p hg
    simpa only [d8138, d164, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41434 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35785 p hg
    simpa only [d8117, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d8117, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41435 (p : Pattern) (guard : d8123 p = 1) : d135 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d135, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41434 p hg
    simpa only [d8123, d135, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d135, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d8123, d135, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41436 (p : Pattern) (guard : d8129 p = 1) : d138 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d138, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41435 p hg
    simpa only [d8129, d138, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d138, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d8129, d138, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41437 (p : Pattern) (guard : d8135 p = 1) : d156 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d156, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41436 p hg
    simpa only [d8135, d156, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d156, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d8135, d156, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41438 (p : Pattern) (guard : d8136 p = 1) : d157 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d157, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38231 p hg
    simpa only [d8136, d157, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d157, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41437 p hg
    simpa only [d8136, d157, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41439 (p : Pattern) (guard : d8142 p = 1) : d165 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d165, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41438 p hg
    simpa only [d8142, d165, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d165, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d165, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
