/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5600 (p : Pattern) (guard : d794 p = 1) : d246 p ≤ (0 : Int) + d1204 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d246, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5597 p hg
    simpa only [d246, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d246, d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d246, d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5601 (p : Pattern) (guard : d794 p = 1) : d247 p ≤ (0 : Int) + d1205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d247, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d247, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d247, d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5600 p hg
    simpa only [d247, d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5602 (p : Pattern) (guard : d794 p = 1) : d248 p ≤ (0 : Int) + d1206 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d248, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5601 p hg
    simpa only [d248, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d248, d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d248, d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5603 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d138, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d138, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d138, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1277 p hg
    simpa only [d138, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5604 (p : Pattern) (guard : d794 p = 1) : d140 p ≤ (0 : Int) + d139 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5603 p hg
    simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5594 p hg
    simpa only [d794, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5605 (p : Pattern) (guard : d794 p = 1) : d188 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d188, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5604 p hg
    simpa only [d188, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d188, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d188, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5606 (p : Pattern) (guard : d1 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare5607 (p : Pattern) (guard : d1 p = 1) : d145 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d145, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d145, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d145, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5606 p hg
    simpa only [d145, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5608 (p : Pattern) (guard : d794 p = 1) : d147 p ≤ (0 : Int) + d146 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5607 p hg
    simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5598 p hg
    simpa only [d794, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5609 (p : Pattern) (guard : d794 p = 1) : d249 p ≤ (0 : Int) + d1208 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d249, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5608 p hg
    simpa only [d249, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d249, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d249, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5610 (p : Pattern) (guard : d794 p = 1) : d250 p ≤ (0 : Int) + d1209 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d250, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5605 p hg
    simpa only [d250, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d250, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5609 p hg
    simpa only [d250, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5611 (p : Pattern) (guard : d794 p = 1) : d251 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d251, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5610 p hg
    simpa only [d251, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d251, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d251, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5612 (p : Pattern) (guard : d794 p = 1) : d252 p ≤ (0 : Int) + d1211 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d252, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5602 p hg
    simpa only [d252, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d252, d1211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5611 p hg
    simpa only [d252, d1211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5613 (p : Pattern) (guard : d794 p = 1) : d191 p ≤ (0 : Int) + d1207 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d191, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5595 p hg
    simpa only [d191, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d191, d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d191, d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5614 (p : Pattern) (guard : d794 p = 1) : d253 p ≤ (0 : Int) + d1208 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d253, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5599 p hg
    simpa only [d253, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d253, d1208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d253, d1208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5615 (p : Pattern) (guard : d794 p = 1) : d254 p ≤ (0 : Int) + d1209 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d254, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5613 p hg
    simpa only [d254, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d254, d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5614 p hg
    simpa only [d254, d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5616 (p : Pattern) (guard : d794 p = 1) : d255 p ≤ (0 : Int) + d1210 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d255, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5615 p hg
    simpa only [d255, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d255, d1210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d255, d1210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5617 (p : Pattern) (guard : d794 p = 1) : d256 p ≤ (0 : Int) + d1212 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d256, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5616 p hg
    simpa only [d256, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d256, d1212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d256, d1212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5618 (p : Pattern) (guard : d794 p = 1) : d257 p ≤ (0 : Int) + d1213 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d257, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5612 p hg
    simpa only [d257, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d257, d1213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5617 p hg
    simpa only [d257, d1213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5619 (p : Pattern) (guard : d794 p = 1) : d258 p ≤ (0 : Int) + d1214 p := by
  cases selected : p 108 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d258, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5592 p hg
    simpa only [d258, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d258, d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5618 p hg
    simpa only [d258, d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5620 (p : Pattern) (guard : d828 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare5621 (p : Pattern) (guard : d1017 p = 1) : d57 p ≤ (0 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5620 p hg
    simpa only [d1017, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3870 p hg
    simpa only [d1017, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5622 (p : Pattern) (guard : d828 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare5623 (p : Pattern) (guard : d1017 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5622 p hg
    simpa only [d1017, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3872 p hg
    simpa only [d1017, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5624 (p : Pattern) (guard : d1017 p = 1) : d64 p ≤ (0 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5625 (p : Pattern) (guard : d828 p = 1) : d7 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5626 (p : Pattern) (guard : d1017 p = 1) : d106 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5625 p hg
    simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5627 (p : Pattern) (guard : d828 p = 1) : d120 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5628 (p : Pattern) (guard : d1017 p = 1) : d121 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d1017, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1017, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5629 (p : Pattern) (guard : d1017 p = 1) : d122 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5628 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5630 (p : Pattern) (guard : d1017 p = 1) : d179 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5626 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5631 (p : Pattern) (guard : d828 p = 1) : d11 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5632 (p : Pattern) (guard : d828 p = 1) : d12 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5625 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d828 p = 1 := by simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5631 p hg
    simpa only [d12, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5633 (p : Pattern) (guard : d1017 p = 1) : d109 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5632 p hg
    simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1017, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5634 (p : Pattern) (guard : d828 p = 1) : d126 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5635 (p : Pattern) (guard : d828 p = 1) : d127 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5627 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d828 p = 1 := by simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5634 p hg
    simpa only [d127, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5636 (p : Pattern) (guard : d1017 p = 1) : d128 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5635 p hg
    simpa only [d1017, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1017, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5637 (p : Pattern) (guard : d1017 p = 1) : d129 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5633 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5636 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5638 (p : Pattern) (guard : d1017 p = 1) : d237 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5633 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5637 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5639 (p : Pattern) (guard : d1017 p = 1) : d238 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d238, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5630 p hg
    simpa only [d238, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d238, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5638 p hg
    simpa only [d238, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5640 (p : Pattern) (guard : d1017 p = 1) : d239 p ≤ (0 : Int) + d838 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d239, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5624 p hg
    simpa only [d239, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d239, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5639 p hg
    simpa only [d239, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5641 (p : Pattern) (guard : d1017 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare5642 (p : Pattern) (guard : d1017 p = 1) : d68 p ≤ (0 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5643 (p : Pattern) (guard : d1017 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare5644 (p : Pattern) (guard : d1017 p = 1) : d69 p ≤ (0 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5645 (p : Pattern) (guard : d1017 p = 1) : d70 p ≤ (0 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5642 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5644 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5646 (p : Pattern) (guard : d1017 p = 1) : d181 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5629 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5647 (p : Pattern) (guard : d1017 p = 1) : d240 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5637 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5648 (p : Pattern) (guard : d1017 p = 1) : d241 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5646 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5647 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5649 (p : Pattern) (guard : d1017 p = 1) : d242 p ≤ (0 : Int) + d839 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d242, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5645 p hg
    simpa only [d242, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d242, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5648 p hg
    simpa only [d242, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5650 (p : Pattern) (guard : d1017 p = 1) : d243 p ≤ (0 : Int) + d840 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d243, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5640 p hg
    simpa only [d243, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d243, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d243, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5651 (p : Pattern) (guard : d1017 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare5652 (p : Pattern) (guard : d1017 p = 1) : d244 p ≤ (0 : Int) + d841 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d244, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5649 p hg
    simpa only [d244, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d244, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d244, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5653 (p : Pattern) (guard : d1017 p = 1) : d245 p ≤ (0 : Int) + d842 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d245, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5650 p hg
    simpa only [d245, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d245, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5652 p hg
    simpa only [d245, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5654 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  omega
theorem compare5655 (p : Pattern) (guard : d828 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5654 p hg
    simpa only [d828, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5656 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5657 (p : Pattern) (guard : d1017 p = 1) : d139 p ≤ (0 : Int) + d119 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5655 p hg
    simpa only [d1017, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d1017, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5658 (p : Pattern) (guard : d1017 p = 1) : d153 p ≤ (0 : Int) + d1215 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d153, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d153, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d153, d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d153, d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5659 (p : Pattern) (guard : d1017 p = 1) : d186 p ≤ (0 : Int) + d1216 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d186, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5621 p hg
    simpa only [d186, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d186, d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d186, d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5660 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  omega
theorem compare5661 (p : Pattern) (guard : d828 p = 1) : d126 p ≤ (0 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5660 p hg
    simpa only [d828, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5662 (p : Pattern) (guard : d828 p = 1) : d127 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5655 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d828 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5663 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5664 (p : Pattern) (guard : d1017 p = 1) : d146 p ≤ (0 : Int) + d502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d1017, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d1017, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5665 (p : Pattern) (guard : d1017 p = 1) : d155 p ≤ (0 : Int) + d1217 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d155, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d155, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d155, d1217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d155, d1217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5666 (p : Pattern) (guard : d1017 p = 1) : d246 p ≤ (0 : Int) + d1218 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d246, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5623 p hg
    simpa only [d246, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d246, d1218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5665 p hg
    simpa only [d246, d1218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5667 (p : Pattern) (guard : d1017 p = 1) : d247 p ≤ (0 : Int) + d1219 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d247, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d247, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d247, d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5666 p hg
    simpa only [d247, d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5668 (p : Pattern) (guard : d1017 p = 1) : d248 p ≤ (0 : Int) + d1220 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d248, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d248, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d248, d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d248, d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5669 (p : Pattern) (guard : d828 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5670 (p : Pattern) (guard : d1017 p = 1) : d138 p ≤ (0 : Int) + d119 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d1017, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5656 p hg
    simpa only [d1017, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5671 (p : Pattern) (guard : d1017 p = 1) : d140 p ≤ (0 : Int) + d119 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5672 (p : Pattern) (guard : d1017 p = 1) : d188 p ≤ (0 : Int) + d1221 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d188, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5671 p hg
    simpa only [d188, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d188, d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d188, d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5673 (p : Pattern) (guard : d828 p = 1) : d11 p ≤ (0 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5674 (p : Pattern) (guard : d828 p = 1) : d12 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d828 p = 1 := by simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d12, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5675 (p : Pattern) (guard : d1017 p = 1) : d145 p ≤ (0 : Int) + d502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5674 p hg
    simpa only [d1017, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d1017, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5676 (p : Pattern) (guard : d1017 p = 1) : d147 p ≤ (0 : Int) + d502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5675 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5664 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5677 (p : Pattern) (guard : d1017 p = 1) : d249 p ≤ (0 : Int) + d1222 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d249, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5676 p hg
    simpa only [d249, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d249, d1222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d249, d1222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5678 (p : Pattern) (guard : d1017 p = 1) : d250 p ≤ (0 : Int) + d1223 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d250, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5672 p hg
    simpa only [d250, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d250, d1223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5677 p hg
    simpa only [d250, d1223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5679 (p : Pattern) (guard : d1017 p = 1) : d251 p ≤ (0 : Int) + d1224 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d251, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d251, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d251, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d251, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5680 (p : Pattern) (guard : d1017 p = 1) : d252 p ≤ (0 : Int) + d1225 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d252, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d252, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d252, d1225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d252, d1225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5681 (p : Pattern) (guard : d1017 p = 1) : d191 p ≤ (0 : Int) + d1226 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d191, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d191, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d191, d1226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5641 p hg
    simpa only [d191, d1226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5682 (p : Pattern) (guard : d1017 p = 1) : d253 p ≤ (0 : Int) + d1227 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d253, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5665 p hg
    simpa only [d253, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d253, d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5643 p hg
    simpa only [d253, d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5683 (p : Pattern) (guard : d1017 p = 1) : d254 p ≤ (0 : Int) + d1228 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d254, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5681 p hg
    simpa only [d254, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d254, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5682 p hg
    simpa only [d254, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5684 (p : Pattern) (guard : d1017 p = 1) : d255 p ≤ (0 : Int) + d1229 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d255, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5683 p hg
    simpa only [d255, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d255, d1229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d255, d1229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5685 (p : Pattern) (guard : d1017 p = 1) : d256 p ≤ (0 : Int) + d1230 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d256, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d256, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d256, d1230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5651 p hg
    simpa only [d256, d1230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5686 (p : Pattern) (guard : d1017 p = 1) : d257 p ≤ (0 : Int) + d1231 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d257, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5680 p hg
    simpa only [d257, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d257, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d257, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5687 (p : Pattern) (guard : d1017 p = 1) : d258 p ≤ (0 : Int) + d1232 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1017 p = 1 := by simpa only [d258, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5653 p hg
    simpa only [d258, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1017 p = 1 := by simpa only [d258, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d258, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5688 (p : Pattern) (guard : d851 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5689 (p : Pattern) (guard : d851 p = 1) : d121 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5690 (p : Pattern) (guard : d851 p = 1) : d122 p ≤ (0 : Int) + d505 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5691 (p : Pattern) (guard : d851 p = 1) : d179 p ≤ (0 : Int) + d505 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5692 (p : Pattern) (guard : d851 p = 1) : d126 p ≤ (0 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5693 (p : Pattern) (guard : d851 p = 1) : d127 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5694 (p : Pattern) (guard : d851 p = 1) : d128 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5695 (p : Pattern) (guard : d851 p = 1) : d129 p ≤ (0 : Int) + d506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5696 (p : Pattern) (guard : d851 p = 1) : d237 p ≤ (0 : Int) + d506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5697 (p : Pattern) (guard : d851 p = 1) : d238 p ≤ (0 : Int) + d507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d238, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d238, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d238, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d238, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5698 (p : Pattern) (guard : d851 p = 1) : d239 p ≤ (0 : Int) + d508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d239, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d239, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d239, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5697 p hg
    simpa only [d239, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5699 (p : Pattern) (guard : d851 p = 1) : d181 p ≤ (0 : Int) + d512 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d181, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d181, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d181, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d181, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5700 (p : Pattern) (guard : d851 p = 1) : d240 p ≤ (0 : Int) + d513 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d240, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d240, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d240, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d240, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5701 (p : Pattern) (guard : d851 p = 1) : d241 p ≤ (0 : Int) + d514 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d241, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d241, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d241, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5700 p hg
    simpa only [d241, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5702 (p : Pattern) (guard : d851 p = 1) : d242 p ≤ (0 : Int) + d515 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d242, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d242, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d242, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d242, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5703 (p : Pattern) (guard : d851 p = 1) : d243 p ≤ (0 : Int) + d516 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d243, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d243, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d243, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d243, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5704 (p : Pattern) (guard : d851 p = 1) : d244 p ≤ (0 : Int) + d517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d244, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5702 p hg
    simpa only [d244, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d244, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d244, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5705 (p : Pattern) (guard : d851 p = 1) : d245 p ≤ (0 : Int) + d518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d245, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d245, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d245, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d245, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5706 (p : Pattern) (guard : d851 p = 1) : d139 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d139, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5688 p hg
    simpa only [d139, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d139, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d139, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5707 (p : Pattern) (guard : d851 p = 1) : d153 p ≤ (0 : Int) + d501 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5706 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5708 (p : Pattern) (guard : d851 p = 1) : d186 p ≤ (0 : Int) + d501 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5709 (p : Pattern) (guard : d851 p = 1) : d146 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d146, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d146, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d146, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d146, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5710 (p : Pattern) (guard : d851 p = 1) : d155 p ≤ (0 : Int) + d503 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5711 (p : Pattern) (guard : d851 p = 1) : d246 p ≤ (0 : Int) + d503 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5712 (p : Pattern) (guard : d851 p = 1) : d247 p ≤ (0 : Int) + d504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d247, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d247, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d247, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5711 p hg
    simpa only [d247, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5713 (p : Pattern) (guard : d851 p = 1) : d248 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d248, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5712 p hg
    simpa only [d248, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d248, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d248, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5714 (p : Pattern) (guard : d851 p = 1) : d138 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d138, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d138, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d138, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d138, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5715 (p : Pattern) (guard : d851 p = 1) : d140 p ≤ (0 : Int) + d501 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5706 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5716 (p : Pattern) (guard : d851 p = 1) : d188 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d188, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5715 p hg
    simpa only [d188, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d188, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d188, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5717 (p : Pattern) (guard : d851 p = 1) : d145 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d145, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d145, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d145, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d145, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5718 (p : Pattern) (guard : d851 p = 1) : d147 p ≤ (0 : Int) + d503 p := by
  cases selected : p 159 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5717 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5719 (p : Pattern) (guard : d851 p = 1) : d249 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d249, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d249, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d249, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d249, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5720 (p : Pattern) (guard : d851 p = 1) : d250 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d250, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5716 p hg
    simpa only [d250, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d250, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d250, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5721 (p : Pattern) (guard : d851 p = 1) : d251 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d251, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5720 p hg
    simpa only [d251, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d251, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d251, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5722 (p : Pattern) (guard : d851 p = 1) : d252 p ≤ (0 : Int) + d521 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d252, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5713 p hg
    simpa only [d252, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d252, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d252, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5723 (p : Pattern) (guard : d851 p = 1) : d191 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d191, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5707 p hg
    simpa only [d191, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d191, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d191, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5724 (p : Pattern) (guard : d851 p = 1) : d253 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d253, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d253, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d253, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d253, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5725 (p : Pattern) (guard : d851 p = 1) : d254 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d254, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5723 p hg
    simpa only [d254, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d254, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5724 p hg
    simpa only [d254, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5726 (p : Pattern) (guard : d851 p = 1) : d255 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d255, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d255, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d255, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d255, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5727 (p : Pattern) (guard : d851 p = 1) : d256 p ≤ (0 : Int) + d522 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d256, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d256, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d256, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d256, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5728 (p : Pattern) (guard : d851 p = 1) : d257 p ≤ (0 : Int) + d523 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d257, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d257, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d257, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d257, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5729 (p : Pattern) (guard : d851 p = 1) : d258 p ≤ (0 : Int) + d524 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d258, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5705 p hg
    simpa only [d258, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d258, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5728 p hg
    simpa only [d258, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5730 (p : Pattern) (guard : d850 p = 1) : d64 p ≤ (2 : Int) + d64 p := by
  omega
theorem compare5731 (p : Pattern) (guard : d850 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  omega
theorem compare5732 (p : Pattern) (guard : d850 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare5733 (p : Pattern) (guard : d850 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d850, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d850, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d850, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d850, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5734 (p : Pattern) (guard : d850 p = 1) : d120 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5733 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5735 (p : Pattern) (guard : d850 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare5736 (p : Pattern) (guard : d850 p = 1) : d121 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5737 (p : Pattern) (guard : d850 p = 1) : d122 p ≤ (2 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5731 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5736 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5738 (p : Pattern) (guard : d850 p = 1) : d179 p ≤ (2 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5731 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5737 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5739 (p : Pattern) (guard : d850 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  omega
end NetHack.Sokoban12CostPartition
