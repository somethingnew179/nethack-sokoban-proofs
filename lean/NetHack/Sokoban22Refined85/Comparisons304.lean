/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons303
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42560 (p : Pattern) (guard : d8101 p = 1) : d2549 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d8101, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d8101, d2549, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42561 (p : Pattern) (guard : d8106 p = 1) : d2588 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42330 p hg
    simpa only [d8106, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2588, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42562 (p : Pattern) (guard : d8107 p = 1) : d2589 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42560 p hg
    simpa only [d8107, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42561 p hg
    simpa only [d8107, d2589, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42563 (p : Pattern) (guard : d8113 p = 1) : d2591 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42562 p hg
    simpa only [d8113, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42169 p hg
    simpa only [d8113, d2591, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42564 (p : Pattern) (guard : d8119 p = 1) : d2597 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42563 p hg
    simpa only [d8119, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42179 p hg
    simpa only [d8119, d2597, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42565 (p : Pattern) (guard : d8120 p = 1) : d2598 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42559 p hg
    simpa only [d8120, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d8120, d2598, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42566 (p : Pattern) (guard : d8121 p = 1) : d2599 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42526 p hg
    simpa only [d8121, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42565 p hg
    simpa only [d8121, d2599, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42567 (p : Pattern) (guard : d8127 p = 1) : d2629 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42566 p hg
    simpa only [d8127, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42366 p hg
    simpa only [d8127, d2629, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42568 (p : Pattern) (guard : d8095 p = 1) : d2600 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42285 p hg
    simpa only [d8095, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2600, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42569 (p : Pattern) (guard : d8096 p = 1) : d2601 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42257 p hg
    simpa only [d8096, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42568 p hg
    simpa only [d8096, d2601, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42570 (p : Pattern) (guard : d8102 p = 1) : d2601 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42569 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42352 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42571 (p : Pattern) (guard : d8107 p = 1) : d2604 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42327 p hg
    simpa only [d8107, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42361 p hg
    simpa only [d8107, d2604, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42572 (p : Pattern) (guard : d8108 p = 1) : d2605 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42570 p hg
    simpa only [d8108, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42571 p hg
    simpa only [d8108, d2605, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42573 (p : Pattern) (guard : d8113 p = 1) : d2609 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42340 p hg
    simpa only [d8113, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42191 p hg
    simpa only [d8113, d2609, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42574 (p : Pattern) (guard : d8114 p = 1) : d2610 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42572 p hg
    simpa only [d8114, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42573 p hg
    simpa only [d8114, d2610, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42575 (p : Pattern) (guard : d8107 p = 1) : d2614 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42020 p hg
    simpa only [d8107, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42202 p hg
    simpa only [d8107, d2614, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42576 (p : Pattern) (guard : d8113 p = 1) : d2615 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42575 p hg
    simpa only [d8113, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2615, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42577 (p : Pattern) (guard : d8119 p = 1) : d2616 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42576 p hg
    simpa only [d8119, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2616, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42578 (p : Pattern) (guard : d8120 p = 1) : d2617 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42574 p hg
    simpa only [d8120, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42577 p hg
    simpa only [d8120, d2617, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42579 (p : Pattern) (guard : d8101 p = 1) : d2601 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42416 p hg
    simpa only [d8101, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d8101, d2601, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42580 (p : Pattern) (guard : d8106 p = 1) : d2611 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42420 p hg
    simpa only [d8106, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d8106, d2611, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42581 (p : Pattern) (guard : d8107 p = 1) : d2618 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42579 p hg
    simpa only [d8107, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42580 p hg
    simpa only [d8107, d2618, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42582 (p : Pattern) (guard : d8106 p = 1) : d2603 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42427 p hg
    simpa only [d8106, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42187 p hg
    simpa only [d8106, d2603, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42583 (p : Pattern) (guard : d8112 p = 1) : d2619 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42582 p hg
    simpa only [d8112, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42215 p hg
    simpa only [d8112, d2619, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42584 (p : Pattern) (guard : d8113 p = 1) : d2620 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42581 p hg
    simpa only [d8113, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42583 p hg
    simpa only [d8113, d2620, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42585 (p : Pattern) (guard : d8112 p = 1) : d2621 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42361 p hg
    simpa only [d8112, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d8112, d2621, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42586 (p : Pattern) (guard : d8118 p = 1) : d2622 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42585 p hg
    simpa only [d8118, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2622, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42587 (p : Pattern) (guard : d8119 p = 1) : d2623 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42584 p hg
    simpa only [d8119, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42586 p hg
    simpa only [d8119, d2623, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42588 (p : Pattern) (guard : d8125 p = 1) : d2627 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42587 p hg
    simpa only [d8125, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d8125, d2627, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42589 (p : Pattern) (guard : d8126 p = 1) : d2628 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42578 p hg
    simpa only [d8126, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42588 p hg
    simpa only [d8126, d2628, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42590 (p : Pattern) (guard : d8101 p = 1) : d2607 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41915 p hg
    simpa only [d8101, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41988 p hg
    simpa only [d8101, d2607, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42591 (p : Pattern) (guard : d8107 p = 1) : d2630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42590 p hg
    simpa only [d8107, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42034 p hg
    simpa only [d8107, d2630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42592 (p : Pattern) (guard : d8113 p = 1) : d2631 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42591 p hg
    simpa only [d8113, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d8113, d2631, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42593 (p : Pattern) (guard : d8119 p = 1) : d2633 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42592 p hg
    simpa only [d8119, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42370 p hg
    simpa only [d8119, d2633, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42594 (p : Pattern) (guard : d8125 p = 1) : d2635 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42593 p hg
    simpa only [d8125, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42372 p hg
    simpa only [d8125, d2635, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42595 (p : Pattern) (guard : d8118 p = 1) : d2632 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42557 p hg
    simpa only [d8118, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2632, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42596 (p : Pattern) (guard : d8124 p = 1) : d2634 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42595 p hg
    simpa only [d8124, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2634, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42597 (p : Pattern) (guard : d8130 p = 1) : d2636 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42596 p hg
    simpa only [d8130, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2636, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42598 (p : Pattern) (guard : d8131 p = 1) : d2637 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42594 p hg
    simpa only [d8131, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42597 p hg
    simpa only [d8131, d2637, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42599 (p : Pattern) (guard : d8132 p = 1) : d2638 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42589 p hg
    simpa only [d8132, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42598 p hg
    simpa only [d8132, d2638, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42600 (p : Pattern) (guard : d8133 p = 1) : d2639 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42567 p hg
    simpa only [d8133, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42599 p hg
    simpa only [d8133, d2639, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42601 (p : Pattern) (guard : d8102 p = 1) : d2640 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42289 p hg
    simpa only [d8102, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42417 p hg
    simpa only [d8102, d2640, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42602 (p : Pattern) (guard : d8107 p = 1) : d2528 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42381 p hg
    simpa only [d8107, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42428 p hg
    simpa only [d8107, d2528, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42603 (p : Pattern) (guard : d8108 p = 1) : d2641 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42601 p hg
    simpa only [d8108, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42602 p hg
    simpa only [d8108, d2641, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42604 (p : Pattern) (guard : d8113 p = 1) : d2538 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42387 p hg
    simpa only [d8113, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42392 p hg
    simpa only [d8113, d2538, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42605 (p : Pattern) (guard : d8114 p = 1) : d2642 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42603 p hg
    simpa only [d8114, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42604 p hg
    simpa only [d8114, d2642, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42606 (p : Pattern) (guard : d8101 p = 1) : d2544 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42239 p hg
    simpa only [d8101, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d8101, d2544, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42607 (p : Pattern) (guard : d8107 p = 1) : d2550 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42606 p hg
    simpa only [d8107, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42400 p hg
    simpa only [d8107, d2550, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42608 (p : Pattern) (guard : d8113 p = 1) : d2557 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42607 p hg
    simpa only [d8113, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42406 p hg
    simpa only [d8113, d2557, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42609 (p : Pattern) (guard : d8119 p = 1) : d2563 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42608 p hg
    simpa only [d8119, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42411 p hg
    simpa only [d8119, d2563, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42610 (p : Pattern) (guard : d8120 p = 1) : d2643 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42605 p hg
    simpa only [d8120, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42609 p hg
    simpa only [d8120, d2643, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42611 (p : Pattern) (guard : d8085 p = 1) : d2504 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d8085, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2504, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42612 (p : Pattern) (guard : d8090 p = 1) : d2504 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42611 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42613 (p : Pattern) (guard : d8095 p = 1) : d2518 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42612 p hg
    simpa only [d8095, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d8095, d2518, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42614 (p : Pattern) (guard : d8101 p = 1) : d2519 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42613 p hg
    simpa only [d8101, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42380 p hg
    simpa only [d8101, d2519, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42615 (p : Pattern) (guard : d8089 p = 1) : d2540 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35043 p hg
    simpa only [d8089, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2540, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42616 (p : Pattern) (guard : d8094 p = 1) : d2540 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42615 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42617 (p : Pattern) (guard : d8100 p = 1) : d2569 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42616 p hg
    simpa only [d8100, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d8100, d2569, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42618 (p : Pattern) (guard : d8106 p = 1) : d2573 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42617 p hg
    simpa only [d8106, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42422 p hg
    simpa only [d8106, d2573, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42619 (p : Pattern) (guard : d8107 p = 1) : d2644 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42614 p hg
    simpa only [d8107, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42618 p hg
    simpa only [d8107, d2644, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42620 (p : Pattern) (guard : d8089 p = 1) : d2520 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35049 p hg
    simpa only [d8089, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2520, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42621 (p : Pattern) (guard : d8094 p = 1) : d2520 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42620 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42622 (p : Pattern) (guard : d8100 p = 1) : d2523 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42621 p hg
    simpa only [d8100, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d8100, d2523, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42623 (p : Pattern) (guard : d8106 p = 1) : d2527 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42622 p hg
    simpa only [d8106, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42385 p hg
    simpa only [d8106, d2527, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42624 (p : Pattern) (guard : d8112 p = 1) : d2575 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42623 p hg
    simpa only [d8112, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42430 p hg
    simpa only [d8112, d2575, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42625 (p : Pattern) (guard : d8113 p = 1) : d2645 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42619 p hg
    simpa only [d8113, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42624 p hg
    simpa only [d8113, d2645, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42626 (p : Pattern) (guard : d8112 p = 1) : d2582 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42428 p hg
    simpa only [d8112, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d8112, d2582, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42627 (p : Pattern) (guard : d8118 p = 1) : d2586 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42626 p hg
    simpa only [d8118, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d8118, d2586, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42628 (p : Pattern) (guard : d8119 p = 1) : d2646 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42625 p hg
    simpa only [d8119, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42627 p hg
    simpa only [d8119, d2646, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42629 (p : Pattern) (guard : d8106 p = 1) : d2549 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42470 p hg
    simpa only [d8106, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d8106, d2549, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42630 (p : Pattern) (guard : d8112 p = 1) : d2589 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42629 p hg
    simpa only [d8112, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42438 p hg
    simpa only [d8112, d2589, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42631 (p : Pattern) (guard : d8118 p = 1) : d2591 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42630 p hg
    simpa only [d8118, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42441 p hg
    simpa only [d8118, d2591, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42632 (p : Pattern) (guard : d8124 p = 1) : d2597 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42631 p hg
    simpa only [d8124, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42446 p hg
    simpa only [d8124, d2597, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42633 (p : Pattern) (guard : d8125 p = 1) : d2647 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42628 p hg
    simpa only [d8125, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42632 p hg
    simpa only [d8125, d2647, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42634 (p : Pattern) (guard : d8126 p = 1) : d2648 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42610 p hg
    simpa only [d8126, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42633 p hg
    simpa only [d8126, d2648, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42635 (p : Pattern) (guard : d8132 p = 1) : d2649 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42634 p hg
    simpa only [d8132, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42501 p hg
    simpa only [d8132, d2649, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42636 (p : Pattern) (guard : d8107 p = 1) : d2601 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42352 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42496 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42637 (p : Pattern) (guard : d8112 p = 1) : d2604 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42471 p hg
    simpa only [d8112, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42454 p hg
    simpa only [d8112, d2604, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42638 (p : Pattern) (guard : d8113 p = 1) : d2605 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42636 p hg
    simpa only [d8113, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42637 p hg
    simpa only [d8113, d2605, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42639 (p : Pattern) (guard : d8119 p = 1) : d2610 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42638 p hg
    simpa only [d8119, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42458 p hg
    simpa only [d8119, d2610, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42640 (p : Pattern) (guard : d8125 p = 1) : d2617 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42639 p hg
    simpa only [d8125, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42466 p hg
    simpa only [d8125, d2617, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42641 (p : Pattern) (guard : d8089 p = 1) : d2504 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35444 p hg
    simpa only [d8089, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2504, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42642 (p : Pattern) (guard : d8094 p = 1) : d2504 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42641 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42396 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42643 (p : Pattern) (guard : d8100 p = 1) : d2518 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42642 p hg
    simpa only [d8100, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42398 p hg
    simpa only [d8100, d2518, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42644 (p : Pattern) (guard : d8106 p = 1) : d2601 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42643 p hg
    simpa only [d8106, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42450 p hg
    simpa only [d8106, d2601, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42645 (p : Pattern) (guard : d8112 p = 1) : d2618 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42644 p hg
    simpa only [d8112, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42473 p hg
    simpa only [d8112, d2618, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42646 (p : Pattern) (guard : d8118 p = 1) : d2620 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42645 p hg
    simpa only [d8118, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42476 p hg
    simpa only [d8118, d2620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42647 (p : Pattern) (guard : d8124 p = 1) : d2623 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42646 p hg
    simpa only [d8124, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42481 p hg
    simpa only [d8124, d2623, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42648 (p : Pattern) (guard : d8130 p = 1) : d2627 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42647 p hg
    simpa only [d8130, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42485 p hg
    simpa only [d8130, d2627, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42649 (p : Pattern) (guard : d8131 p = 1) : d2628 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42640 p hg
    simpa only [d8131, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42648 p hg
    simpa only [d8131, d2628, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42650 (p : Pattern) (guard : d8137 p = 1) : d2650 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42649 p hg
    simpa only [d8137, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2650, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42651 (p : Pattern) (guard : d8138 p = 1) : d2651 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42635 p hg
    simpa only [d8138, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42650 p hg
    simpa only [d8138, d2651, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42652 (p : Pattern) (guard : d8139 p = 1) : d2652 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42600 p hg
    simpa only [d8139, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42651 p hg
    simpa only [d8139, d2652, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42653 (p : Pattern) (guard : d1 p = 1) : d2676 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35086 p hg
    simpa only [d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d2676, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42654 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35092 p hg
    simpa only [d8085, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42655 (p : Pattern) (guard : d8086 p = 1) : d2678 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42653 p hg
    simpa only [d8086, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42654 p hg
    simpa only [d8086, d2678, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42656 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35088 p hg
    simpa only [d8085, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42657 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42658 (p : Pattern) (guard : d8084 p = 1) : d1940 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42657 p hg
    simpa only [d8084, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42659 (p : Pattern) (guard : d8089 p = 1) : d2679 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42658 p hg
    simpa only [d8089, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42660 (p : Pattern) (guard : d8090 p = 1) : d2680 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42656 p hg
    simpa only [d8090, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42659 p hg
    simpa only [d8090, d2680, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42661 (p : Pattern) (guard : d8091 p = 1) : d2681 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42655 p hg
    simpa only [d8091, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42660 p hg
    simpa only [d8091, d2681, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42662 (p : Pattern) (guard : d8089 p = 1) : d2682 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d8089, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42663 (p : Pattern) (guard : d8090 p = 1) : d2683 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42654 p hg
    simpa only [d8090, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42662 p hg
    simpa only [d8090, d2683, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42664 (p : Pattern) (guard : d8095 p = 1) : d2684 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42663 p hg
    simpa only [d8095, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2684, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42665 (p : Pattern) (guard : d8096 p = 1) : d2685 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42661 p hg
    simpa only [d8096, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42664 p hg
    simpa only [d8096, d2685, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42666 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35108 p hg
    simpa only [d8085, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42667 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d8089, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42668 (p : Pattern) (guard : d8090 p = 1) : d2677 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42666 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42667 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42669 (p : Pattern) (guard : d8089 p = 1) : d2677 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8089, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42670 (p : Pattern) (guard : d5854 p = 1) : d2679 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39234 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42671 (p : Pattern) (guard : d8094 p = 1) : d2680 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8094, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42670 p hg
    simpa only [d8094, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42672 (p : Pattern) (guard : d8095 p = 1) : d2686 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42668 p hg
    simpa only [d8095, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d8095, d2686, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42673 (p : Pattern) (guard : d5854 p = 1) : d2682 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42674 (p : Pattern) (guard : d8094 p = 1) : d2683 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42667 p hg
    simpa only [d8094, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42673 p hg
    simpa only [d8094, d2683, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42675 (p : Pattern) (guard : d8100 p = 1) : d2684 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42674 p hg
    simpa only [d8100, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2684, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42676 (p : Pattern) (guard : d8101 p = 1) : d2687 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42672 p hg
    simpa only [d8101, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42675 p hg
    simpa only [d8101, d2687, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42677 (p : Pattern) (guard : d8102 p = 1) : d2688 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42665 p hg
    simpa only [d8102, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42676 p hg
    simpa only [d8102, d2688, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42678 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35122 p hg
    simpa only [d8085, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42679 (p : Pattern) (guard : d8090 p = 1) : d2677 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42678 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42680 (p : Pattern) (guard : d8095 p = 1) : d2686 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42679 p hg
    simpa only [d8095, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d8095, d2686, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42681 (p : Pattern) (guard : d8094 p = 1) : d2683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8094, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42673 p hg
    simpa only [d8094, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42682 (p : Pattern) (guard : d8100 p = 1) : d2684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42681 p hg
    simpa only [d8100, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42683 (p : Pattern) (guard : d8101 p = 1) : d2687 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42680 p hg
    simpa only [d8101, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42682 p hg
    simpa only [d8101, d2687, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42684 (p : Pattern) (guard : d8089 p = 1) : d2689 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35131 p hg
    simpa only [d8089, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2689, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42685 (p : Pattern) (guard : d5854 p = 1) : d2689 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5854, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42686 (p : Pattern) (guard : d8094 p = 1) : d2689 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42684 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42687 (p : Pattern) (guard : d8099 p = 1) : d2691 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8099, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21851 p hg
    simpa only [d8099, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42688 (p : Pattern) (guard : d8100 p = 1) : d2692 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42686 p hg
    simpa only [d8100, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42687 p hg
    simpa only [d8100, d2692, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42689 (p : Pattern) (guard : d8099 p = 1) : d2694 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8099, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21854 p hg
    simpa only [d8099, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42690 (p : Pattern) (guard : d8105 p = 1) : d2695 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42689 p hg
    simpa only [d8105, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42691 (p : Pattern) (guard : d8106 p = 1) : d2696 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42688 p hg
    simpa only [d8106, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42690 p hg
    simpa only [d8106, d2696, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42692 (p : Pattern) (guard : d8107 p = 1) : d2697 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42683 p hg
    simpa only [d8107, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42691 p hg
    simpa only [d8107, d2697, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42693 (p : Pattern) (guard : d8108 p = 1) : d2698 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42677 p hg
    simpa only [d8108, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42692 p hg
    simpa only [d8108, d2698, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42694 (p : Pattern) (guard : d8085 p = 1) : d2677 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35145 p hg
    simpa only [d8085, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41787 p hg
    simpa only [d8085, d2677, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42695 (p : Pattern) (guard : d8090 p = 1) : d2677 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42694 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42669 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42696 (p : Pattern) (guard : d8095 p = 1) : d2686 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42695 p hg
    simpa only [d8095, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42671 p hg
    simpa only [d8095, d2686, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42697 (p : Pattern) (guard : d8101 p = 1) : d2687 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42696 p hg
    simpa only [d8101, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42682 p hg
    simpa only [d8101, d2687, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42698 (p : Pattern) (guard : d8089 p = 1) : d2689 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35151 p hg
    simpa only [d8089, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d8089, d2689, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42699 (p : Pattern) (guard : d8094 p = 1) : d2689 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42698 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42685 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
