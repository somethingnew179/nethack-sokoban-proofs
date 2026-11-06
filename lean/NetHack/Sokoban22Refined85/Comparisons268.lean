/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons267
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37520 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37519 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37521 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37520 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37522 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37521 p hg
    simpa only [d8100, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37523 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37522 p hg
    simpa only [d8106, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37524 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34583 p hg
    simpa only [d5843, d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37525 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37524 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37526 (p : Pattern) (guard : d5854 p = 1) : d30 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37525 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37527 (p : Pattern) (guard : d8099 p = 1) : d30 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37526 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37528 (p : Pattern) (guard : d8105 p = 1) : d3643 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37527 p hg
    simpa only [d8105, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d8105, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37529 (p : Pattern) (guard : d8111 p = 1) : d3678 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37528 p hg
    simpa only [d8111, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d8111, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37530 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37523 p hg
    simpa only [d8112, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37529 p hg
    simpa only [d8112, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37531 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d5843, d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37532 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37531 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37533 (p : Pattern) (guard : d5854 p = 1) : d17 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37532 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37534 (p : Pattern) (guard : d8099 p = 1) : d17 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37533 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37535 (p : Pattern) (guard : d8105 p = 1) : d3605 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37534 p hg
    simpa only [d8105, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36691 p hg
    simpa only [d8105, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37536 (p : Pattern) (guard : d8111 p = 1) : d3670 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37535 p hg
    simpa only [d8111, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36755 p hg
    simpa only [d8111, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37537 (p : Pattern) (guard : d8117 p = 1) : d3686 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37536 p hg
    simpa only [d8117, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d8117, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37538 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37530 p hg
    simpa only [d8118, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37537 p hg
    simpa only [d8118, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37539 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37538 p hg
    simpa only [d8124, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d8124, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37540 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37539 p hg
    simpa only [d8130, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37541 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37518 p hg
    simpa only [d8131, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37540 p hg
    simpa only [d8131, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37542 (p : Pattern) (guard : d8106 p = 1) : d3674 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36565 p hg
    simpa only [d8106, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36232 p hg
    simpa only [d8106, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37543 (p : Pattern) (guard : d8112 p = 1) : d3697 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37542 p hg
    simpa only [d8112, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36472 p hg
    simpa only [d8112, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37544 (p : Pattern) (guard : d8118 p = 1) : d3698 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37543 p hg
    simpa only [d8118, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37545 (p : Pattern) (guard : d8123 p = 1) : d3699 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8123, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37546 (p : Pattern) (guard : d8124 p = 1) : d3700 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37544 p hg
    simpa only [d8124, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37545 p hg
    simpa only [d8124, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37547 (p : Pattern) (guard : d8129 p = 1) : d3701 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37545 p hg
    simpa only [d8129, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37548 (p : Pattern) (guard : d8130 p = 1) : d3702 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37546 p hg
    simpa only [d8130, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37547 p hg
    simpa only [d8130, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37549 (p : Pattern) (guard : d8135 p = 1) : d3703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37547 p hg
    simpa only [d8135, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37550 (p : Pattern) (guard : d8136 p = 1) : d3704 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37548 p hg
    simpa only [d8136, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37549 p hg
    simpa only [d8136, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37551 (p : Pattern) (guard : d8137 p = 1) : d3705 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37541 p hg
    simpa only [d8137, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37550 p hg
    simpa only [d8137, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37552 (p : Pattern) (guard : d8138 p = 1) : d3730 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37506 p hg
    simpa only [d8138, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37551 p hg
    simpa only [d8138, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37553 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37412 p hg
    simpa only [d8095, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37554 (p : Pattern) (guard : d8100 p = 1) : d3659 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37441 p hg
    simpa only [d8100, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37555 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37553 p hg
    simpa only [d8101, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37554 p hg
    simpa only [d8101, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37556 (p : Pattern) (guard : d8099 p = 1) : d3657 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36684 p hg
    simpa only [d8099, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31646 p hg
    simpa only [d8099, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37557 (p : Pattern) (guard : d8100 p = 1) : d3658 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37521 p hg
    simpa only [d8100, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d8100, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37558 (p : Pattern) (guard : d5854 p = 1) : d3544 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d5854, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d5854, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37559 (p : Pattern) (guard : d8099 p = 1) : d3545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37558 p hg
    simpa only [d8099, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d8099, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37560 (p : Pattern) (guard : d8105 p = 1) : d3659 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d8105, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37561 (p : Pattern) (guard : d8106 p = 1) : d3660 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37557 p hg
    simpa only [d8106, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37560 p hg
    simpa only [d8106, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37562 (p : Pattern) (guard : d8107 p = 1) : d3660 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37555 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37561 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37563 (p : Pattern) (guard : d8100 p = 1) : d3658 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37492 p hg
    simpa only [d8100, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d8100, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37564 (p : Pattern) (guard : d8106 p = 1) : d3660 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37563 p hg
    simpa only [d8106, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37560 p hg
    simpa only [d8106, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37565 (p : Pattern) (guard : d0 p = 1) : d3873 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37566 (p : Pattern) (guard : d8105 p = 1) : d3874 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3874, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37534 p hg
    simpa only [d8105, d3874, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3874, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37565 p hg
    simpa only [d8105, d3874, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37567 (p : Pattern) (guard : d0 p = 1) : d3875 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37568 (p : Pattern) (guard : d8111 p = 1) : d3876 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3876, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37566 p hg
    simpa only [d8111, d3876, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3876, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37567 p hg
    simpa only [d8111, d3876, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37569 (p : Pattern) (guard : d8112 p = 1) : d3877 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3877, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37564 p hg
    simpa only [d8112, d3877, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3877, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37568 p hg
    simpa only [d8112, d3877, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37570 (p : Pattern) (guard : d8113 p = 1) : d3878 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3878, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37562 p hg
    simpa only [d8113, d3878, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3878, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37569 p hg
    simpa only [d8113, d3878, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37571 (p : Pattern) (guard : d8100 p = 1) : d3658 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36966 p hg
    simpa only [d8100, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d8100, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37572 (p : Pattern) (guard : d8106 p = 1) : d3660 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37571 p hg
    simpa only [d8106, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37560 p hg
    simpa only [d8106, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37573 (p : Pattern) (guard : d8105 p = 1) : d3874 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36690 p hg
    simpa only [d8105, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37565 p hg
    simpa only [d8105, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37574 (p : Pattern) (guard : d8111 p = 1) : d3876 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37573 p hg
    simpa only [d8111, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37567 p hg
    simpa only [d8111, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37575 (p : Pattern) (guard : d8112 p = 1) : d3877 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3877, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37572 p hg
    simpa only [d8112, d3877, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3877, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37574 p hg
    simpa only [d8112, d3877, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37576 (p : Pattern) (guard : d8118 p = 1) : d3879 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3879, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37575 p hg
    simpa only [d8118, d3879, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3879, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d8118, d3879, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37577 (p : Pattern) (guard : d8119 p = 1) : d3880 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3880, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37570 p hg
    simpa only [d8119, d3880, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3880, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37576 p hg
    simpa only [d8119, d3880, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37578 (p : Pattern) (guard : d8111 p = 1) : d3881 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36731 p hg
    simpa only [d8111, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d8111, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37579 (p : Pattern) (guard : d8112 p = 1) : d3882 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3882, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36628 p hg
    simpa only [d8112, d3882, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3882, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37578 p hg
    simpa only [d8112, d3882, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37580 (p : Pattern) (guard : d8111 p = 1) : d3883 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36731 p hg
    simpa only [d8111, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36471 p hg
    simpa only [d8111, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37581 (p : Pattern) (guard : d0 p = 1) : d3884 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37582 (p : Pattern) (guard : d8117 p = 1) : d3885 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37580 p hg
    simpa only [d8117, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37581 p hg
    simpa only [d8117, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37583 (p : Pattern) (guard : d8118 p = 1) : d3886 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3886, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37579 p hg
    simpa only [d8118, d3886, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3886, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37582 p hg
    simpa only [d8118, d3886, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37584 (p : Pattern) (guard : d8117 p = 1) : d3887 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36732 p hg
    simpa only [d8117, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37581 p hg
    simpa only [d8117, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37585 (p : Pattern) (guard : d8123 p = 1) : d3888 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37584 p hg
    simpa only [d8123, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36739 p hg
    simpa only [d8123, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37586 (p : Pattern) (guard : d8124 p = 1) : d3889 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3889, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37583 p hg
    simpa only [d8124, d3889, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3889, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37585 p hg
    simpa only [d8124, d3889, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37587 (p : Pattern) (guard : d8125 p = 1) : d3890 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3890, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37577 p hg
    simpa only [d8125, d3890, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3890, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37586 p hg
    simpa only [d8125, d3890, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37588 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37589 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37588 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37590 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37589 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37591 (p : Pattern) (guard : d8100 p = 1) : d3658 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37590 p hg
    simpa only [d8100, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d8100, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37592 (p : Pattern) (guard : d8106 p = 1) : d3660 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37591 p hg
    simpa only [d8106, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37560 p hg
    simpa only [d8106, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37593 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d5843, d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d30, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37594 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37593 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37595 (p : Pattern) (guard : d5854 p = 1) : d30 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37594 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37596 (p : Pattern) (guard : d8099 p = 1) : d30 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37595 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37597 (p : Pattern) (guard : d0 p = 1) : d3892 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37598 (p : Pattern) (guard : d8105 p = 1) : d3893 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3893, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37596 p hg
    simpa only [d8105, d3893, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3893, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37597 p hg
    simpa only [d8105, d3893, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37599 (p : Pattern) (guard : d0 p = 1) : d3894 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37600 (p : Pattern) (guard : d8111 p = 1) : d3895 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3895, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37598 p hg
    simpa only [d8111, d3895, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3895, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37599 p hg
    simpa only [d8111, d3895, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37601 (p : Pattern) (guard : d8112 p = 1) : d3896 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3896, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37592 p hg
    simpa only [d8112, d3896, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3896, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37600 p hg
    simpa only [d8112, d3896, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37602 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d5843, d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37603 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37602 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37604 (p : Pattern) (guard : d5854 p = 1) : d17 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37603 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37605 (p : Pattern) (guard : d8099 p = 1) : d17 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37604 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37606 (p : Pattern) (guard : d8105 p = 1) : d3874 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3874, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37605 p hg
    simpa only [d8105, d3874, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3874, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37565 p hg
    simpa only [d8105, d3874, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37607 (p : Pattern) (guard : d8111 p = 1) : d3876 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3876, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37606 p hg
    simpa only [d8111, d3876, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3876, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37567 p hg
    simpa only [d8111, d3876, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37608 (p : Pattern) (guard : d8117 p = 1) : d3897 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3897, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37607 p hg
    simpa only [d8117, d3897, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3897, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d8117, d3897, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37609 (p : Pattern) (guard : d8118 p = 1) : d3898 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3898, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37601 p hg
    simpa only [d8118, d3898, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3898, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37608 p hg
    simpa only [d8118, d3898, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37610 (p : Pattern) (guard : d8117 p = 1) : d3899 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3899, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37568 p hg
    simpa only [d8117, d3899, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3899, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3899, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37611 (p : Pattern) (guard : d8123 p = 1) : d3900 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3900, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37610 p hg
    simpa only [d8123, d3900, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3900, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d8123, d3900, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37612 (p : Pattern) (guard : d8124 p = 1) : d3901 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37609 p hg
    simpa only [d8124, d3901, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3901, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37611 p hg
    simpa only [d8124, d3901, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37613 (p : Pattern) (guard : d0 p = 1) : d3606 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37614 (p : Pattern) (guard : d8117 p = 1) : d3902 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37578 p hg
    simpa only [d8117, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37613 p hg
    simpa only [d8117, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37615 (p : Pattern) (guard : d0 p = 1) : d3903 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37616 (p : Pattern) (guard : d8123 p = 1) : d3904 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37614 p hg
    simpa only [d8123, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37615 p hg
    simpa only [d8123, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37617 (p : Pattern) (guard : d0 p = 1) : d3906 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37618 (p : Pattern) (guard : d8129 p = 1) : d3907 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37616 p hg
    simpa only [d8129, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37617 p hg
    simpa only [d8129, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37619 (p : Pattern) (guard : d8130 p = 1) : d3908 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3908, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37612 p hg
    simpa only [d8130, d3908, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3908, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37618 p hg
    simpa only [d8130, d3908, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37620 (p : Pattern) (guard : d8131 p = 1) : d3909 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3909, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37587 p hg
    simpa only [d8131, d3909, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3909, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37619 p hg
    simpa only [d8131, d3909, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37621 (p : Pattern) (guard : d8100 p = 1) : d3910 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3910, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36966 p hg
    simpa only [d8100, d3910, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3910, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36749 p hg
    simpa only [d8100, d3910, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37622 (p : Pattern) (guard : d8105 p = 1) : d3911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37556 p hg
    simpa only [d8105, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37623 (p : Pattern) (guard : d8106 p = 1) : d3912 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3912, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37621 p hg
    simpa only [d8106, d3912, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3912, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37622 p hg
    simpa only [d8106, d3912, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37624 (p : Pattern) (guard : d8099 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37625 (p : Pattern) (guard : d0 p = 1) : d3581 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37626 (p : Pattern) (guard : d8105 p = 1) : d3582 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37624 p hg
    simpa only [d8105, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37625 p hg
    simpa only [d8105, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37627 (p : Pattern) (guard : d0 p = 1) : d3667 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37628 (p : Pattern) (guard : d8111 p = 1) : d3668 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37626 p hg
    simpa only [d8111, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37627 p hg
    simpa only [d8111, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37629 (p : Pattern) (guard : d8112 p = 1) : d3913 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3913, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37623 p hg
    simpa only [d8112, d3913, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3913, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37628 p hg
    simpa only [d8112, d3913, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37630 (p : Pattern) (guard : d0 p = 1) : d3680 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37631 (p : Pattern) (guard : d8117 p = 1) : d3681 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36777 p hg
    simpa only [d8117, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37630 p hg
    simpa only [d8117, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37632 (p : Pattern) (guard : d8118 p = 1) : d3914 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37629 p hg
    simpa only [d8118, d3914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3914, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37631 p hg
    simpa only [d8118, d3914, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37633 (p : Pattern) (guard : d8123 p = 1) : d3682 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37631 p hg
    simpa only [d8123, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d8123, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37634 (p : Pattern) (guard : d8124 p = 1) : d3915 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3915, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37632 p hg
    simpa only [d8124, d3915, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3915, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37633 p hg
    simpa only [d8124, d3915, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37635 (p : Pattern) (guard : d0 p = 1) : d3920 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37636 (p : Pattern) (guard : d8117 p = 1) : d3921 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8117, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37635 p hg
    simpa only [d8117, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37637 (p : Pattern) (guard : d8123 p = 1) : d3922 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37636 p hg
    simpa only [d8123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37638 (p : Pattern) (guard : d8129 p = 1) : d3923 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37637 p hg
    simpa only [d8129, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37639 (p : Pattern) (guard : d8130 p = 1) : d3924 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3924, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37634 p hg
    simpa only [d8130, d3924, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3924, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37638 p hg
    simpa only [d8130, d3924, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37640 (p : Pattern) (guard : d0 p = 1) : d3928 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37641 (p : Pattern) (guard : d8111 p = 1) : d3929 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3929, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37499 p hg
    simpa only [d8111, d3929, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3929, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37640 p hg
    simpa only [d8111, d3929, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37642 (p : Pattern) (guard : d0 p = 1) : d3678 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37643 (p : Pattern) (guard : d8117 p = 1) : d3930 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3930, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37641 p hg
    simpa only [d8117, d3930, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3930, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37642 p hg
    simpa only [d8117, d3930, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37644 (p : Pattern) (guard : d0 p = 1) : d3931 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37645 (p : Pattern) (guard : d8123 p = 1) : d3932 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3932, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37643 p hg
    simpa only [d8123, d3932, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3932, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37644 p hg
    simpa only [d8123, d3932, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37646 (p : Pattern) (guard : d0 p = 1) : d3692 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37647 (p : Pattern) (guard : d8129 p = 1) : d3933 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3933, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37645 p hg
    simpa only [d8129, d3933, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3933, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37646 p hg
    simpa only [d8129, d3933, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37648 (p : Pattern) (guard : d0 p = 1) : d3936 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37649 (p : Pattern) (guard : d8135 p = 1) : d3937 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3937, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37647 p hg
    simpa only [d8135, d3937, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3937, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37648 p hg
    simpa only [d8135, d3937, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37650 (p : Pattern) (guard : d8136 p = 1) : d3938 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3938, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37639 p hg
    simpa only [d8136, d3938, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3938, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37649 p hg
    simpa only [d8136, d3938, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37651 (p : Pattern) (guard : d8137 p = 1) : d3939 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3939, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37620 p hg
    simpa only [d8137, d3939, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3939, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37650 p hg
    simpa only [d8137, d3939, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37652 (p : Pattern) (guard : d8100 p = 1) : d3910 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3910, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37492 p hg
    simpa only [d8100, d3910, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3910, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36749 p hg
    simpa only [d8100, d3910, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37653 (p : Pattern) (guard : d8106 p = 1) : d3912 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3912, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37652 p hg
    simpa only [d8106, d3912, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3912, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37622 p hg
    simpa only [d8106, d3912, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37654 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d5843, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37655 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37654 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37656 (p : Pattern) (guard : d5854 p = 1) : d13 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37655 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37657 (p : Pattern) (guard : d8099 p = 1) : d13 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37656 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37658 (p : Pattern) (guard : d8105 p = 1) : d3582 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37657 p hg
    simpa only [d8105, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37625 p hg
    simpa only [d8105, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37659 (p : Pattern) (guard : d8111 p = 1) : d3668 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37658 p hg
    simpa only [d8111, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37627 p hg
    simpa only [d8111, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
