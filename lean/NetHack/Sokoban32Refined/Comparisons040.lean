/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5600 (p : Pattern) (guard : d1126 p = 1) : d440 p ≤ (0 : Int) + d247 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d440, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d440, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d440, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d440, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5601 (p : Pattern) (guard : d0 p = 1) : d444 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5602 (p : Pattern) (guard : d1122 p = 1) : d445 p ≤ (0 : Int) + d248 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d445, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d1122, d445, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d445, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5601 p hg
    simpa only [d1122, d445, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5603 (p : Pattern) (guard : d0 p = 1) : d447 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5604 (p : Pattern) (guard : d1125 p = 1) : d448 p ≤ (0 : Int) + d249 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d448, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d1125, d448, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d448, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5603 p hg
    simpa only [d1125, d448, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5605 (p : Pattern) (guard : d1126 p = 1) : d449 p ≤ (0 : Int) + d250 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d449, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5602 p hg
    simpa only [d1126, d449, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d449, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5604 p hg
    simpa only [d1126, d449, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5606 (p : Pattern) (guard : d0 p = 1) : d419 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5607 (p : Pattern) (guard : d1122 p = 1) : d450 p ≤ (0 : Int) + d251 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d1122, d450, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d1122, d450, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d450, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5606 p hg
    simpa only [d1122, d450, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5608 (p : Pattern) (guard : d1125 p = 1) : d451 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1125, d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d1125, d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1125, d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1125, d451, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5609 (p : Pattern) (guard : d1126 p = 1) : d452 p ≤ (0 : Int) + d252 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1122 p = 1 := by simpa only [d1126, d452, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5607 p hg
    simpa only [d1126, d452, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, d452, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5608 p hg
    simpa only [d1126, d452, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5610 (p : Pattern) (guard : d1126 p = 1) : d453 p ≤ (0 : Int) + d253 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d453, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5605 p hg
    simpa only [d453, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d453, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5609 p hg
    simpa only [d453, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5611 (p : Pattern) (guard : d1126 p = 1) : d454 p ≤ (0 : Int) + d254 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d454, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d454, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d454, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5610 p hg
    simpa only [d454, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5612 (p : Pattern) (guard : d1126 p = 1) : d455 p ≤ (0 : Int) + d255 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d455, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d455, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d455, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5611 p hg
    simpa only [d455, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5613 (p : Pattern) (guard : d1088 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare5614 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d1092, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d1092, d389, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5615 (p : Pattern) (guard : d1088 p = 1) : d20 p ≤ (0 : Int) + d20 p := by
  omega
theorem compare5616 (p : Pattern) (guard : d1092 p = 1) : d390 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d1092, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d1092, d390, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5617 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5616 p hg
    simpa only [d391, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5618 (p : Pattern) (guard : d1092 p = 1) : d392 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d392, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5619 (p : Pattern) (guard : d1088 p = 1) : d33 p ≤ (0 : Int) + d33 p := by
  omega
theorem compare5620 (p : Pattern) (guard : d1092 p = 1) : d393 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d1092, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d1092, d393, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5621 (p : Pattern) (guard : d1092 p = 1) : d394 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5620 p hg
    simpa only [d394, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5622 (p : Pattern) (guard : d1088 p = 1) : d38 p ≤ (0 : Int) + d38 p := by
  omega
theorem compare5623 (p : Pattern) (guard : d1092 p = 1) : d395 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d1092, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d1092, d395, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5624 (p : Pattern) (guard : d1092 p = 1) : d396 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5616 p hg
    simpa only [d396, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5625 (p : Pattern) (guard : d1092 p = 1) : d397 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5624 p hg
    simpa only [d397, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5626 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5625 p hg
    simpa only [d398, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5627 (p : Pattern) (guard : d1092 p = 1) : d399 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d1092, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d399, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5628 (p : Pattern) (guard : d1092 p = 1) : d400 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2062 p hg
    simpa only [d1092, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d1092, d400, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5629 (p : Pattern) (guard : d1092 p = 1) : d401 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5628 p hg
    simpa only [d401, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5630 (p : Pattern) (guard : d1092 p = 1) : d402 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d402, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5631 (p : Pattern) (guard : d1092 p = 1) : d403 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2066 p hg
    simpa only [d1092, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d403, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5632 (p : Pattern) (guard : d1092 p = 1) : d404 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5631 p hg
    simpa only [d404, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5633 (p : Pattern) (guard : d1092 p = 1) : d405 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2069 p hg
    simpa only [d1092, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1092, d405, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5634 (p : Pattern) (guard : d1092 p = 1) : d406 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5633 p hg
    simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5628 p hg
    simpa only [d406, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5635 (p : Pattern) (guard : d1092 p = 1) : d407 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5632 p hg
    simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5634 p hg
    simpa only [d407, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5636 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5630 p hg
    simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5635 p hg
    simpa only [d408, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5637 (p : Pattern) (guard : d1092 p = 1) : d408 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5636 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5638 (p : Pattern) (guard : d1092 p = 1) : d409 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5637 p hg
    simpa only [d409, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5639 (p : Pattern) (guard : d1092 p = 1) : d413 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5579 p hg
    simpa only [d413, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5640 (p : Pattern) (guard : d1092 p = 1) : d414 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5639 p hg
    simpa only [d414, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5641 (p : Pattern) (guard : d1092 p = 1) : d415 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d415, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5642 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d416, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5643 (p : Pattern) (guard : d1092 p = 1) : d417 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5640 p hg
    simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d417, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5644 (p : Pattern) (guard : d1092 p = 1) : d418 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d418, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5645 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5630 p hg
    simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5644 p hg
    simpa only [d419, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5646 (p : Pattern) (guard : d1092 p = 1) : d419 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5645 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5647 (p : Pattern) (guard : d1092 p = 1) : d420 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5646 p hg
    simpa only [d420, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5648 (p : Pattern) (guard : d1092 p = 1) : d421 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5638 p hg
    simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5647 p hg
    simpa only [d421, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5649 (p : Pattern) (guard : d1092 p = 1) : d389 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d1092, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d1092, d389, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5650 (p : Pattern) (guard : d1092 p = 1) : d390 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d1092, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d1092, d390, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5651 (p : Pattern) (guard : d1092 p = 1) : d391 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5650 p hg
    simpa only [d391, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5652 (p : Pattern) (guard : d1092 p = 1) : d392 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d392, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5653 (p : Pattern) (guard : d1092 p = 1) : d393 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5619 p hg
    simpa only [d1092, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d393, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5654 (p : Pattern) (guard : d1092 p = 1) : d394 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5653 p hg
    simpa only [d394, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5655 (p : Pattern) (guard : d1092 p = 1) : d395 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d1092, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d1092, d395, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5656 (p : Pattern) (guard : d1092 p = 1) : d396 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5655 p hg
    simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5650 p hg
    simpa only [d396, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5657 (p : Pattern) (guard : d1092 p = 1) : d397 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5654 p hg
    simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d397, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5658 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d398, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5659 (p : Pattern) (guard : d1092 p = 1) : d398 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5660 (p : Pattern) (guard : d1092 p = 1) : d427 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d427, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5661 (p : Pattern) (guard : d1092 p = 1) : d415 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1687 p hg
    simpa only [d415, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5662 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d416, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5663 (p : Pattern) (guard : d1092 p = 1) : d416 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5664 (p : Pattern) (guard : d1092 p = 1) : d435 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5588 p hg
    simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d435, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5665 (p : Pattern) (guard : d1092 p = 1) : d436 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d436, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5666 (p : Pattern) (guard : d1092 p = 1) : d437 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5660 p hg
    simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5665 p hg
    simpa only [d437, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5667 (p : Pattern) (guard : d1092 p = 1) : d438 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5648 p hg
    simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5666 p hg
    simpa only [d438, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5668 (p : Pattern) (guard : d1092 p = 1) : d439 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5646 p hg
    simpa only [d439, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5669 (p : Pattern) (guard : d1092 p = 1) : d440 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5638 p hg
    simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d440, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5670 (p : Pattern) (guard : d1088 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  omega
theorem compare5671 (p : Pattern) (guard : d1092 p = 1) : d441 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d1092, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d1092, d441, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5672 (p : Pattern) (guard : d1092 p = 1) : d442 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5671 p hg
    simpa only [d442, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5673 (p : Pattern) (guard : d1092 p = 1) : d443 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5672 p hg
    simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d443, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5674 (p : Pattern) (guard : d1092 p = 1) : d444 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d444, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5675 (p : Pattern) (guard : d1092 p = 1) : d445 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5674 p hg
    simpa only [d445, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5676 (p : Pattern) (guard : d1092 p = 1) : d448 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d448, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5677 (p : Pattern) (guard : d1092 p = 1) : d449 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5675 p hg
    simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5676 p hg
    simpa only [d449, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5678 (p : Pattern) (guard : d1092 p = 1) : d450 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5645 p hg
    simpa only [d450, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5679 (p : Pattern) (guard : d1092 p = 1) : d452 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5468 p hg
    simpa only [d452, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5680 (p : Pattern) (guard : d1092 p = 1) : d453 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d453, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5681 (p : Pattern) (guard : d1092 p = 1) : d454 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5680 p hg
    simpa only [d454, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5682 (p : Pattern) (guard : d1092 p = 1) : d455 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5681 p hg
    simpa only [d455, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5683 (p : Pattern) (guard : d0 p = 1) : d135 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5684 (p : Pattern) (guard : d1088 p = 1) : d456 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5683 p hg
    simpa only [d1088, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5685 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5686 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d52, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d52, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d52, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d1088, d52, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5687 (p : Pattern) (guard : d1088 p = 1) : d457 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d457, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5688 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5689 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5690 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5691 (p : Pattern) (guard : d1088 p = 1) : d458 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5692 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5693 (p : Pattern) (guard : d1088 p = 1) : d459 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d1088, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5694 (p : Pattern) (guard : d1088 p = 1) : d460 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d460, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5695 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5696 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5697 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5698 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d54, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d1088, d54, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d54, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d1088, d54, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5699 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5700 (p : Pattern) (guard : d1088 p = 1) : d461 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d461, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5701 (p : Pattern) (guard : d1088 p = 1) : d462 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5700 p hg
    simpa only [d462, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5702 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5703 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d1088, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5704 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d58, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d1088, d58, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5705 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5706 (p : Pattern) (guard : d1088 p = 1) : d463 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5705 p hg
    simpa only [d463, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5707 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5708 (p : Pattern) (guard : d1088 p = 1) : d464 p ≤ (0 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d1088, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5709 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5710 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d61, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d61, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d61, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d1088, d61, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5711 (p : Pattern) (guard : d1088 p = 1) : d465 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d465, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5712 (p : Pattern) (guard : d1088 p = 1) : d466 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5711 p hg
    simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d466, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5713 (p : Pattern) (guard : d1088 p = 1) : d467 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5706 p hg
    simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5712 p hg
    simpa only [d467, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5714 (p : Pattern) (guard : d1088 p = 1) : d468 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5713 p hg
    simpa only [d468, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5715 (p : Pattern) (guard : d0 p = 1) : d468 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5716 (p : Pattern) (guard : d1095 p = 1) : d468 p ≤ (0 : Int) + d228 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d1095, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5717 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5718 (p : Pattern) (guard : d1088 p = 1) : d459 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d459, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d459, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d459, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5717 p hg
    simpa only [d1088, d459, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5719 (p : Pattern) (guard : d1088 p = 1) : d460 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5720 (p : Pattern) (guard : d1088 p = 1) : d469 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5721 (p : Pattern) (guard : d1088 p = 1) : d470 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5722 (p : Pattern) (guard : d1088 p = 1) : d471 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5720 p hg
    simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5723 (p : Pattern) (guard : d1088 p = 1) : d472 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d472, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5724 (p : Pattern) (guard : d1088 p = 1) : d473 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d473, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5725 (p : Pattern) (guard : d1088 p = 1) : d474 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5723 p hg
    simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5724 p hg
    simpa only [d474, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5726 (p : Pattern) (guard : d1088 p = 1) : d475 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d475, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5727 (p : Pattern) (guard : d0 p = 1) : d475 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5728 (p : Pattern) (guard : d1095 p = 1) : d475 p ≤ (0 : Int) + d229 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d1095, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5729 (p : Pattern) (guard : d1095 p = 1) : d476 p ≤ (0 : Int) + d230 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d476, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5716 p hg
    simpa only [d476, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d476, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5728 p hg
    simpa only [d476, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5730 (p : Pattern) (guard : d1088 p = 1) : d477 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d477, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5687 p hg
    simpa only [d477, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d477, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d477, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5731 (p : Pattern) (guard : d0 p = 1) : d138 p ≤ (0 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5732 (p : Pattern) (guard : d1088 p = 1) : d478 p ≤ (0 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5731 p hg
    simpa only [d1088, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5733 (p : Pattern) (guard : d1088 p = 1) : d479 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d479, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d479, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d479, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d479, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5734 (p : Pattern) (guard : d1088 p = 1) : d70 p ≤ (0 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d1088, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5735 (p : Pattern) (guard : d1088 p = 1) : d70 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1636 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5736 (p : Pattern) (guard : d1088 p = 1) : d480 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d480, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5733 p hg
    simpa only [d480, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d480, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d480, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5737 (p : Pattern) (guard : d1088 p = 1) : d481 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d481, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d481, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d481, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5736 p hg
    simpa only [d481, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5738 (p : Pattern) (guard : d1088 p = 1) : d482 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d482, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d482, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d482, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5737 p hg
    simpa only [d482, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5739 (p : Pattern) (guard : d0 p = 1) : d487 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban32Refined
