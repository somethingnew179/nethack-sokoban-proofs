/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons068
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9660 (p : Pattern) (guard : d4148 p = 1) : d1261 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1261, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9601 p hg
    simpa only [d1261, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1261, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9622 p hg
    simpa only [d1261, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9661 (p : Pattern) (guard : d4149 p = 1) : d1262 p ≤ (2 : Int) + d52 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9659 p hg
    simpa only [d4149, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9660 p hg
    simpa only [d4149, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9662 (p : Pattern) (guard : d0 p = 1) : d1264 p ≤ (2 : Int) + d82 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9663 (p : Pattern) (guard : d4149 p = 1) : d1265 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9662 p hg
    simpa only [d4149, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9630 p hg
    simpa only [d4149, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9664 (p : Pattern) (guard : d4149 p = 1) : d1266 p ≤ (2 : Int) + d4797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1266, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9661 p hg
    simpa only [d1266, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1266, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9663 p hg
    simpa only [d1266, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9665 (p : Pattern) (guard : d4149 p = 1) : d1267 p ≤ (2 : Int) + d4800 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1267, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9631 p hg
    simpa only [d1267, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1267, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1267, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9666 (p : Pattern) (guard : d4149 p = 1) : d1268 p ≤ (2 : Int) + d4801 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1268, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9664 p hg
    simpa only [d1268, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1268, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9665 p hg
    simpa only [d1268, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9667 (p : Pattern) (guard : d4149 p = 1) : d1269 p ≤ (2 : Int) + d4802 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1269, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1269, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1269, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9666 p hg
    simpa only [d1269, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9668 (p : Pattern) (guard : d4149 p = 1) : d1270 p ≤ (2 : Int) + d4802 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9667 p hg
    simpa only [d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9669 (p : Pattern) (guard : d0 p = 1) : d1282 p ≤ (2 : Int) + d131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9670 (p : Pattern) (guard : d0 p = 1) : d368 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9671 (p : Pattern) (guard : d4148 p = 1) : d1283 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9670 p hg
    simpa only [d4148, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9672 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9673 (p : Pattern) (guard : d4148 p = 1) : d1284 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1284, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d1284, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1284, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9672 p hg
    simpa only [d4148, d1284, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9674 (p : Pattern) (guard : d4148 p = 1) : d1285 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1285, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9671 p hg
    simpa only [d1285, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1285, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9673 p hg
    simpa only [d1285, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9675 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9676 (p : Pattern) (guard : d4148 p = 1) : d1286 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1286, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d1286, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1286, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9675 p hg
    simpa only [d4148, d1286, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9677 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d4148, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9678 (p : Pattern) (guard : d4148 p = 1) : d1287 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1287, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9676 p hg
    simpa only [d1287, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1287, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9677 p hg
    simpa only [d1287, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9679 (p : Pattern) (guard : d4148 p = 1) : d1288 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1288, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9674 p hg
    simpa only [d1288, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1288, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9678 p hg
    simpa only [d1288, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9680 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9681 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6793 p hg
    simpa only [d4148, d1289, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9680 p hg
    simpa only [d4148, d1289, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9682 (p : Pattern) (guard : d1 p = 1) : d139 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d139, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d139, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d139, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d139, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9683 (p : Pattern) (guard : d4148 p = 1) : d1290 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1290, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9682 p hg
    simpa only [d4148, d1290, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1290, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d4148, d1290, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9684 (p : Pattern) (guard : d4148 p = 1) : d1291 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1291, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9681 p hg
    simpa only [d1291, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1291, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1291, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9685 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9686 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9685 p hg
    simpa only [d4148, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9687 (p : Pattern) (guard : d4148 p = 1) : d1292 p ≤ (2 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1292, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9683 p hg
    simpa only [d1292, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1292, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9686 p hg
    simpa only [d1292, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9688 (p : Pattern) (guard : d4148 p = 1) : d1293 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1293, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9684 p hg
    simpa only [d1293, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1293, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9687 p hg
    simpa only [d1293, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9689 (p : Pattern) (guard : d4148 p = 1) : d1294 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1294, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9679 p hg
    simpa only [d1294, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1294, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1294, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9690 (p : Pattern) (guard : d4149 p = 1) : d1295 p ≤ (2 : Int) + d131 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9669 p hg
    simpa only [d4149, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9689 p hg
    simpa only [d4149, d1295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9691 (p : Pattern) (guard : d0 p = 1) : d1302 p ≤ (2 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9692 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9693 (p : Pattern) (guard : d4148 p = 1) : d1303 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9692 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9694 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d1289, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d4148, d1289, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9695 (p : Pattern) (guard : d4148 p = 1) : d1304 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1304, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9693 p hg
    simpa only [d1304, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1304, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1304, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9696 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1300, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9677 p hg
    simpa only [d1300, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9697 (p : Pattern) (guard : d4148 p = 1) : d1305 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1305, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9695 p hg
    simpa only [d1305, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1305, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1305, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9698 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9699 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9698 p hg
    simpa only [d4148, d1289, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9700 (p : Pattern) (guard : d4148 p = 1) : d1300 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9699 p hg
    simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1300, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9701 (p : Pattern) (guard : d4148 p = 1) : d1301 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9700 p hg
    simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1301, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9702 (p : Pattern) (guard : d4148 p = 1) : d1306 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1306, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9697 p hg
    simpa only [d1306, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1306, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9701 p hg
    simpa only [d1306, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9703 (p : Pattern) (guard : d4149 p = 1) : d1307 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9691 p hg
    simpa only [d4149, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9702 p hg
    simpa only [d4149, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9704 (p : Pattern) (guard : d4149 p = 1) : d1308 p ≤ (2 : Int) + d4803 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1308, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9690 p hg
    simpa only [d1308, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1308, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9703 p hg
    simpa only [d1308, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9705 (p : Pattern) (guard : d0 p = 1) : d1311 p ≤ (2 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9706 (p : Pattern) (guard : d0 p = 1) : d370 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9707 (p : Pattern) (guard : d4148 p = 1) : d1312 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9706 p hg
    simpa only [d4148, d1312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9708 (p : Pattern) (guard : d4148 p = 1) : d1313 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1313, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9707 p hg
    simpa only [d1313, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1313, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1313, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9709 (p : Pattern) (guard : d4148 p = 1) : d1314 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1314, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9708 p hg
    simpa only [d1314, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1314, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1314, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9710 (p : Pattern) (guard : d4148 p = 1) : d1315 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1315, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9709 p hg
    simpa only [d1315, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1315, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9701 p hg
    simpa only [d1315, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9711 (p : Pattern) (guard : d4149 p = 1) : d1316 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9705 p hg
    simpa only [d4149, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9710 p hg
    simpa only [d4149, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9712 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (2 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9713 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9677 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9714 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9713 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9715 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9714 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9716 (p : Pattern) (guard : d4149 p = 1) : d162 p ≤ (2 : Int) + d161 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9712 p hg
    simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9715 p hg
    simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9717 (p : Pattern) (guard : d4149 p = 1) : d1317 p ≤ (2 : Int) + d4804 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1317, d4804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9711 p hg
    simpa only [d1317, d4804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1317, d4804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9716 p hg
    simpa only [d1317, d4804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9718 (p : Pattern) (guard : d4149 p = 1) : d1318 p ≤ (2 : Int) + d4805 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1318, d4805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9704 p hg
    simpa only [d1318, d4805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1318, d4805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9717 p hg
    simpa only [d1318, d4805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9719 (p : Pattern) (guard : d0 p = 1) : d1325 p ≤ (2 : Int) + d131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9720 (p : Pattern) (guard : d0 p = 1) : d360 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9721 (p : Pattern) (guard : d4148 p = 1) : d1274 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9720 p hg
    simpa only [d4148, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9722 (p : Pattern) (guard : d4148 p = 1) : d1326 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1326, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9721 p hg
    simpa only [d1326, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1326, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1326, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9723 (p : Pattern) (guard : d4148 p = 1) : d1327 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9722 p hg
    simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1327, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9724 (p : Pattern) (guard : d4148 p = 1) : d1328 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1328, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9723 p hg
    simpa only [d1328, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1328, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1328, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9725 (p : Pattern) (guard : d4149 p = 1) : d1329 p ≤ (2 : Int) + d131 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9719 p hg
    simpa only [d4149, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9724 p hg
    simpa only [d4149, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9726 (p : Pattern) (guard : d0 p = 1) : d1331 p ≤ (2 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9727 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9728 (p : Pattern) (guard : d4148 p = 1) : d1296 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9727 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9729 (p : Pattern) (guard : d4148 p = 1) : d1332 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9728 p hg
    simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9730 (p : Pattern) (guard : d4148 p = 1) : d1333 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1333, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9729 p hg
    simpa only [d1333, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1333, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1333, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9731 (p : Pattern) (guard : d4148 p = 1) : d1334 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9730 p hg
    simpa only [d1334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1334, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9701 p hg
    simpa only [d1334, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9732 (p : Pattern) (guard : d4149 p = 1) : d1335 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9726 p hg
    simpa only [d4149, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9731 p hg
    simpa only [d4149, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9733 (p : Pattern) (guard : d4149 p = 1) : d1336 p ≤ (2 : Int) + d4803 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1336, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9725 p hg
    simpa only [d1336, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1336, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9732 p hg
    simpa only [d1336, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9734 (p : Pattern) (guard : d0 p = 1) : d1339 p ≤ (2 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9735 (p : Pattern) (guard : d4149 p = 1) : d1340 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9734 p hg
    simpa only [d4149, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9731 p hg
    simpa only [d4149, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9736 (p : Pattern) (guard : d4149 p = 1) : d1341 p ≤ (2 : Int) + d4806 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1341, d4806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9735 p hg
    simpa only [d1341, d4806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1341, d4806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1341, d4806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9737 (p : Pattern) (guard : d4149 p = 1) : d1342 p ≤ (2 : Int) + d4807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1342, d4807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9733 p hg
    simpa only [d1342, d4807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1342, d4807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9736 p hg
    simpa only [d1342, d4807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9738 (p : Pattern) (guard : d4149 p = 1) : d1343 p ≤ (2 : Int) + d4808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1343, d4808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9718 p hg
    simpa only [d1343, d4808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1343, d4808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9737 p hg
    simpa only [d1343, d4808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9739 (p : Pattern) (guard : d4149 p = 1) : d1344 p ≤ (2 : Int) + d4809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1344, d4809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1344, d4809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1344, d4809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9738 p hg
    simpa only [d1344, d4809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9740 (p : Pattern) (guard : d4149 p = 1) : d1345 p ≤ (2 : Int) + d4810 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1345, d4810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9668 p hg
    simpa only [d1345, d4810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1345, d4810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9739 p hg
    simpa only [d1345, d4810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9741 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9626 p hg
    simpa only [d4148, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9742 (p : Pattern) (guard : d4148 p = 1) : d1181 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9741 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9585 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9743 (p : Pattern) (guard : d4148 p = 1) : d1346 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1346, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9742 p hg
    simpa only [d1346, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1346, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9587 p hg
    simpa only [d1346, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9744 (p : Pattern) (guard : d4148 p = 1) : d1347 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1347, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d4148, d1347, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1347, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9589 p hg
    simpa only [d4148, d1347, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9745 (p : Pattern) (guard : d4148 p = 1) : d1348 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1348, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9744 p hg
    simpa only [d1348, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1348, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9591 p hg
    simpa only [d1348, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9746 (p : Pattern) (guard : d4148 p = 1) : d1349 p ≤ (2 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1349, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9745 p hg
    simpa only [d1349, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1349, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1349, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9747 (p : Pattern) (guard : d4148 p = 1) : d1350 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1350, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9743 p hg
    simpa only [d1350, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1350, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9746 p hg
    simpa only [d1350, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9748 (p : Pattern) (guard : d4149 p = 1) : d1351 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9662 p hg
    simpa only [d4149, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9747 p hg
    simpa only [d4149, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9749 (p : Pattern) (guard : d4149 p = 1) : d1352 p ≤ (2 : Int) + d4797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1352, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9661 p hg
    simpa only [d1352, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1352, d4797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9748 p hg
    simpa only [d1352, d4797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9750 (p : Pattern) (guard : d4149 p = 1) : d1353 p ≤ (2 : Int) + d82 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9625 p hg
    simpa only [d4149, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9747 p hg
    simpa only [d4149, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9751 (p : Pattern) (guard : d4149 p = 1) : d1354 p ≤ (2 : Int) + d4800 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1354, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9750 p hg
    simpa only [d1354, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1354, d4800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1354, d4800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9752 (p : Pattern) (guard : d4149 p = 1) : d1355 p ≤ (2 : Int) + d4801 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1355, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9749 p hg
    simpa only [d1355, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1355, d4801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9751 p hg
    simpa only [d1355, d4801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9753 (p : Pattern) (guard : d4149 p = 1) : d1356 p ≤ (2 : Int) + d4802 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1356, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9658 p hg
    simpa only [d1356, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1356, d4802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9752 p hg
    simpa only [d1356, d4802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9754 (p : Pattern) (guard : d4149 p = 1) : d1357 p ≤ (2 : Int) + d4802 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9753 p hg
    simpa only [d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9755 (p : Pattern) (guard : d4148 p = 1) : d1358 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1358, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9671 p hg
    simpa only [d1358, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1358, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9694 p hg
    simpa only [d1358, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9756 (p : Pattern) (guard : d4148 p = 1) : d1359 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1359, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9755 p hg
    simpa only [d1359, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1359, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9696 p hg
    simpa only [d1359, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9757 (p : Pattern) (guard : d4148 p = 1) : d1360 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1360, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9756 p hg
    simpa only [d1360, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1360, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9688 p hg
    simpa only [d1360, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9758 (p : Pattern) (guard : d4149 p = 1) : d1361 p ≤ (2 : Int) + d131 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9669 p hg
    simpa only [d4149, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9757 p hg
    simpa only [d4149, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9759 (p : Pattern) (guard : d4149 p = 1) : d1362 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9691 p hg
    simpa only [d4149, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9731 p hg
    simpa only [d4149, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9760 (p : Pattern) (guard : d4149 p = 1) : d1363 p ≤ (2 : Int) + d4803 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1363, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9758 p hg
    simpa only [d1363, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1363, d4803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9759 p hg
    simpa only [d1363, d4803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9761 (p : Pattern) (guard : d4149 p = 1) : d1364 p ≤ (2 : Int) + d152 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9705 p hg
    simpa only [d4149, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9731 p hg
    simpa only [d4149, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9762 (p : Pattern) (guard : d4149 p = 1) : d1365 p ≤ (2 : Int) + d4804 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1365, d4804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9761 p hg
    simpa only [d1365, d4804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1365, d4804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9716 p hg
    simpa only [d1365, d4804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9763 (p : Pattern) (guard : d4149 p = 1) : d1366 p ≤ (2 : Int) + d4805 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1366, d4805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9760 p hg
    simpa only [d1366, d4805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1366, d4805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9762 p hg
    simpa only [d1366, d4805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9764 (p : Pattern) (guard : d0 p = 1) : d1374 p ≤ (2 : Int) + d281 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9765 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d270 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9766 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (2 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6901 p hg
    simpa only [d4148, d1289, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9765 p hg
    simpa only [d4148, d1289, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9767 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (2 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d282, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d282, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9768 (p : Pattern) (guard : d1 p = 1) : d283 p ≤ (2 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d283, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9767 p hg
    simpa only [d283, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d283, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d283, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9769 (p : Pattern) (guard : d4148 p = 1) : d1375 p ≤ (2 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1375, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9768 p hg
    simpa only [d4148, d1375, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1375, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6905 p hg
    simpa only [d4148, d1375, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9770 (p : Pattern) (guard : d4148 p = 1) : d1376 p ≤ (2 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1376, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9766 p hg
    simpa only [d1376, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1376, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9769 p hg
    simpa only [d1376, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9771 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9772 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (2 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9771 p hg
    simpa only [d4148, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4148, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9773 (p : Pattern) (guard : d4148 p = 1) : d1377 p ≤ (2 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1377, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9769 p hg
    simpa only [d1377, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1377, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d1377, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9774 (p : Pattern) (guard : d4148 p = 1) : d1378 p ≤ (2 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1378, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9770 p hg
    simpa only [d1378, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1378, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9773 p hg
    simpa only [d1378, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9775 (p : Pattern) (guard : d4148 p = 1) : d1379 p ≤ (2 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1379, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9730 p hg
    simpa only [d1379, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1379, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9774 p hg
    simpa only [d1379, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9776 (p : Pattern) (guard : d4149 p = 1) : d1380 p ≤ (2 : Int) + d281 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9764 p hg
    simpa only [d4149, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9775 p hg
    simpa only [d4149, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9777 (p : Pattern) (guard : d0 p = 1) : d1384 p ≤ (2 : Int) + d297 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9778 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9779 (p : Pattern) (guard : d4148 p = 1) : d1289 p ≤ (2 : Int) + d291 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1289, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d1289, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1289, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9778 p hg
    simpa only [d4148, d1289, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9780 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (2 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9767 p hg
    simpa only [d298, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d298, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9781 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d292 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9782 (p : Pattern) (guard : d4148 p = 1) : d1385 p ≤ (2 : Int) + d293 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1385, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9780 p hg
    simpa only [d4148, d1385, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1385, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9781 p hg
    simpa only [d4148, d1385, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9783 (p : Pattern) (guard : d4148 p = 1) : d1386 p ≤ (2 : Int) + d294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1386, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9779 p hg
    simpa only [d1386, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1386, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9782 p hg
    simpa only [d1386, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9784 (p : Pattern) (guard : d4148 p = 1) : d1387 p ≤ (2 : Int) + d295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1387, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9782 p hg
    simpa only [d1387, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1387, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9772 p hg
    simpa only [d1387, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9785 (p : Pattern) (guard : d4148 p = 1) : d1388 p ≤ (2 : Int) + d296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1388, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9783 p hg
    simpa only [d1388, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1388, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9784 p hg
    simpa only [d1388, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9786 (p : Pattern) (guard : d4148 p = 1) : d211 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d211, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d4148, d211, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d211, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9698 p hg
    simpa only [d4148, d211, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9787 (p : Pattern) (guard : d4148 p = 1) : d213 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d213, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9786 p hg
    simpa only [d213, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d213, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d213, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9788 (p : Pattern) (guard : d4148 p = 1) : d1389 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1389, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9787 p hg
    simpa only [d1389, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1389, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d1389, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9789 (p : Pattern) (guard : d4148 p = 1) : d1390 p ≤ (2 : Int) + d297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d1390, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9785 p hg
    simpa only [d1390, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d1390, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9788 p hg
    simpa only [d1390, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9790 (p : Pattern) (guard : d4149 p = 1) : d1391 p ≤ (2 : Int) + d297 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9777 p hg
    simpa only [d4149, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9789 p hg
    simpa only [d4149, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9791 (p : Pattern) (guard : d4149 p = 1) : d1392 p ≤ (2 : Int) + d4811 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1392, d4811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9776 p hg
    simpa only [d1392, d4811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1392, d4811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d1392, d4811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9792 (p : Pattern) (guard : d4149 p = 1) : d1393 p ≤ (2 : Int) + d4812 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1393, d4812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9790 p hg
    simpa only [d1393, d4812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1393, d4812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9635 p hg
    simpa only [d1393, d4812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9793 (p : Pattern) (guard : d4149 p = 1) : d1394 p ≤ (2 : Int) + d4813 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1394, d4813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9791 p hg
    simpa only [d1394, d4813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1394, d4813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9792 p hg
    simpa only [d1394, d4813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9794 (p : Pattern) (guard : d4149 p = 1) : d1395 p ≤ (2 : Int) + d4814 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1395, d4814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9763 p hg
    simpa only [d1395, d4814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1395, d4814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9793 p hg
    simpa only [d1395, d4814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9795 (p : Pattern) (guard : d4149 p = 1) : d1396 p ≤ (2 : Int) + d4815 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1396, d4815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9638 p hg
    simpa only [d1396, d4815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1396, d4815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9794 p hg
    simpa only [d1396, d4815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9796 (p : Pattern) (guard : d4149 p = 1) : d1397 p ≤ (2 : Int) + d4816 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1397, d4816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9754 p hg
    simpa only [d1397, d4816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1397, d4816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9795 p hg
    simpa only [d1397, d4816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9797 (p : Pattern) (guard : d4149 p = 1) : d1398 p ≤ (2 : Int) + d4817 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d1398, d4817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9740 p hg
    simpa only [d1398, d4817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d1398, d4817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9796 p hg
    simpa only [d1398, d4817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9798 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9799 (p : Pattern) (guard : d4148 p = 1) : d1154 p ≤ (0 : Int) + d950 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1154, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9798 p hg
    simpa only [d4148, d1154, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
