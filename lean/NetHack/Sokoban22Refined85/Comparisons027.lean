/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3780 (p : Pattern) (guard : d4148 p = 1) : d151 p ≤ (0 : Int) + d1301 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d151, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d151, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d151, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d151, d1301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3781 (p : Pattern) (guard : d4148 p = 1) : d152 p ≤ (0 : Int) + d1302 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d152, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d152, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d152, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d152, d1302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3782 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (0 : Int) + d1306 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3783 (p : Pattern) (guard : d4303 p = 1) : d681 p ≤ (0 : Int) + d1307 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d681, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d4303, d681, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d681, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3782 p hg
    simpa only [d4303, d681, d1307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3784 (p : Pattern) (guard : d4303 p = 1) : d682 p ≤ (0 : Int) + d1308 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d682, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3769 p hg
    simpa only [d682, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d682, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3783 p hg
    simpa only [d682, d1308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3785 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3786 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3785 p hg
    simpa only [d4148, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3787 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1309 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d111, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d111, d1309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3788 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1310 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3787 p hg
    simpa only [d114, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3789 (p : Pattern) (guard : d4148 p = 1) : d152 p ≤ (0 : Int) + d1311 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d152, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d152, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d152, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d152, d1311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3790 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (0 : Int) + d1315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3791 (p : Pattern) (guard : d4303 p = 1) : d683 p ≤ (0 : Int) + d1316 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d683, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3789 p hg
    simpa only [d4303, d683, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d683, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3790 p hg
    simpa only [d4303, d683, d1316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3792 (p : Pattern) (guard : d4303 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare3793 (p : Pattern) (guard : d4303 p = 1) : d684 p ≤ (0 : Int) + d1317 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d684, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d684, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d684, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d684, d1317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3794 (p : Pattern) (guard : d4303 p = 1) : d685 p ≤ (0 : Int) + d1318 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d685, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d685, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d685, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d685, d1318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3795 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3796 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1319 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3795 p hg
    simpa only [d4148, d1319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3797 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3798 (p : Pattern) (guard : d4148 p = 1) : d110 p ≤ (0 : Int) + d1303 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d110, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d110, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d110, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3797 p hg
    simpa only [d4148, d110, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3799 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1320 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d111, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3798 p hg
    simpa only [d111, d1320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3800 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1321 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3799 p hg
    simpa only [d114, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3801 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3802 (p : Pattern) (guard : d4148 p = 1) : d123 p ≤ (0 : Int) + d1322 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d123, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d123, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d123, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3801 p hg
    simpa only [d4148, d123, d1322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3803 (p : Pattern) (guard : d4148 p = 1) : d127 p ≤ (0 : Int) + d1323 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d127, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3802 p hg
    simpa only [d127, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d127, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d127, d1323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3804 (p : Pattern) (guard : d4148 p = 1) : d130 p ≤ (0 : Int) + d1324 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d130, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3803 p hg
    simpa only [d130, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d130, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d130, d1324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3805 (p : Pattern) (guard : d4148 p = 1) : d131 p ≤ (0 : Int) + d1325 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d131, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3800 p hg
    simpa only [d131, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d131, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3804 p hg
    simpa only [d131, d1325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3806 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (0 : Int) + d1328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3807 (p : Pattern) (guard : d4303 p = 1) : d686 p ≤ (0 : Int) + d1329 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d686, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3805 p hg
    simpa only [d4303, d686, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d686, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3806 p hg
    simpa only [d4303, d686, d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3808 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3809 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d4148, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3810 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3811 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1330 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d114, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3812 (p : Pattern) (guard : d4148 p = 1) : d152 p ≤ (0 : Int) + d1331 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d152, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d152, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d152, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d152, d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3813 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3814 (p : Pattern) (guard : d4303 p = 1) : d687 p ≤ (0 : Int) + d1335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d687, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3812 p hg
    simpa only [d4303, d687, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d687, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3813 p hg
    simpa only [d4303, d687, d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3815 (p : Pattern) (guard : d4303 p = 1) : d688 p ≤ (0 : Int) + d1336 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d688, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3807 p hg
    simpa only [d688, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d688, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d688, d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3816 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3817 (p : Pattern) (guard : d4148 p = 1) : d105 p ≤ (0 : Int) + d1303 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d4148, d1303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3818 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1337 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3817 p hg
    simpa only [d111, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d111, d1337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3819 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1338 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3818 p hg
    simpa only [d114, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3820 (p : Pattern) (guard : d4148 p = 1) : d152 p ≤ (0 : Int) + d1339 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d152, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3819 p hg
    simpa only [d152, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d152, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d152, d1339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3821 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3822 (p : Pattern) (guard : d4303 p = 1) : d689 p ≤ (0 : Int) + d1340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d689, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3820 p hg
    simpa only [d4303, d689, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d689, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3821 p hg
    simpa only [d4303, d689, d1340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3823 (p : Pattern) (guard : d4303 p = 1) : d690 p ≤ (0 : Int) + d1341 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d690, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3822 p hg
    simpa only [d690, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d690, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d690, d1341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3824 (p : Pattern) (guard : d4303 p = 1) : d691 p ≤ (0 : Int) + d1342 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d691, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3815 p hg
    simpa only [d691, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d691, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3823 p hg
    simpa only [d691, d1342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3825 (p : Pattern) (guard : d4303 p = 1) : d692 p ≤ (0 : Int) + d1343 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d692, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3794 p hg
    simpa only [d692, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d692, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3824 p hg
    simpa only [d692, d1343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3826 (p : Pattern) (guard : d4303 p = 1) : d693 p ≤ (0 : Int) + d1344 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d693, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d693, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d693, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3825 p hg
    simpa only [d693, d1344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3827 (p : Pattern) (guard : d4303 p = 1) : d694 p ≤ (0 : Int) + d1345 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d694, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3746 p hg
    simpa only [d694, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d694, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3826 p hg
    simpa only [d694, d1345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3828 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (0 : Int) + d1350 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3829 (p : Pattern) (guard : d4303 p = 1) : d674 p ≤ (0 : Int) + d1351 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d674, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d4303, d674, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d674, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3828 p hg
    simpa only [d4303, d674, d1351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3830 (p : Pattern) (guard : d4303 p = 1) : d675 p ≤ (0 : Int) + d1352 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d675, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3734 p hg
    simpa only [d675, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d675, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d675, d1352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3831 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (0 : Int) + d1350 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3832 (p : Pattern) (guard : d4303 p = 1) : d661 p ≤ (0 : Int) + d1353 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d661, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d4303, d661, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d661, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3831 p hg
    simpa only [d4303, d661, d1353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3833 (p : Pattern) (guard : d4303 p = 1) : d676 p ≤ (0 : Int) + d1354 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d676, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d676, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d676, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d676, d1354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3834 (p : Pattern) (guard : d4303 p = 1) : d677 p ≤ (0 : Int) + d1355 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d677, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d677, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d677, d1355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d677, d1355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3835 (p : Pattern) (guard : d4303 p = 1) : d678 p ≤ (0 : Int) + d1356 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d678, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d678, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d678, d1356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d678, d1356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3836 (p : Pattern) (guard : d4303 p = 1) : d679 p ≤ (0 : Int) + d1357 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d679, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d679, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d679, d1357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3835 p hg
    simpa only [d679, d1357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3837 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d1360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3838 (p : Pattern) (guard : d4303 p = 1) : d695 p ≤ (0 : Int) + d1361 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d695, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3767 p hg
    simpa only [d4303, d695, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d695, d1361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3837 p hg
    simpa only [d4303, d695, d1361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3839 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (0 : Int) + d1334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3840 (p : Pattern) (guard : d4303 p = 1) : d696 p ≤ (0 : Int) + d1362 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d696, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d4303, d696, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d696, d1362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3839 p hg
    simpa only [d4303, d696, d1362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3841 (p : Pattern) (guard : d4303 p = 1) : d697 p ≤ (0 : Int) + d1363 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d697, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3838 p hg
    simpa only [d697, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d697, d1363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3840 p hg
    simpa only [d697, d1363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3842 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (0 : Int) + d1334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3843 (p : Pattern) (guard : d4303 p = 1) : d698 p ≤ (0 : Int) + d1364 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d698, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3789 p hg
    simpa only [d4303, d698, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d698, d1364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3842 p hg
    simpa only [d4303, d698, d1364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3844 (p : Pattern) (guard : d4303 p = 1) : d699 p ≤ (0 : Int) + d1365 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d699, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3843 p hg
    simpa only [d699, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d699, d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d699, d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3845 (p : Pattern) (guard : d4303 p = 1) : d700 p ≤ (0 : Int) + d1366 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d700, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3841 p hg
    simpa only [d700, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d700, d1366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3844 p hg
    simpa only [d700, d1366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3846 (p : Pattern) (guard : d4148 p = 1) : d111 p ≤ (0 : Int) + d1367 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d111, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d111, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d111, d1367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d111, d1367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3847 (p : Pattern) (guard : d4148 p = 1) : d114 p ≤ (0 : Int) + d1368 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d114, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d114, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d114, d1368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d114, d1368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3848 (p : Pattern) (guard : d0 p = 1) : d270 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3849 (p : Pattern) (guard : d4148 p = 1) : d271 p ≤ (0 : Int) + d1369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d271, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d271, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d271, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3848 p hg
    simpa only [d4148, d271, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3850 (p : Pattern) (guard : d1 p = 1) : d272 p ≤ (0 : Int) + d272 p := by
  omega
theorem compare3851 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3852 (p : Pattern) (guard : d4148 p = 1) : d275 p ≤ (0 : Int) + d1370 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d275, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d4148, d275, d1370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d275, d1370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3851 p hg
    simpa only [d4148, d275, d1370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3853 (p : Pattern) (guard : d4148 p = 1) : d276 p ≤ (0 : Int) + d1371 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d276, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3849 p hg
    simpa only [d276, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d276, d1371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d276, d1371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3854 (p : Pattern) (guard : d4148 p = 1) : d278 p ≤ (0 : Int) + d278 p := by
  omega
theorem compare3855 (p : Pattern) (guard : d4148 p = 1) : d279 p ≤ (0 : Int) + d1372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d279, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d279, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d279, d1372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d279, d1372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3856 (p : Pattern) (guard : d4148 p = 1) : d280 p ≤ (0 : Int) + d1373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d280, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3853 p hg
    simpa only [d280, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d280, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d280, d1373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3857 (p : Pattern) (guard : d4148 p = 1) : d281 p ≤ (0 : Int) + d1374 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d281, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3847 p hg
    simpa only [d281, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d281, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3856 p hg
    simpa only [d281, d1374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3858 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (0 : Int) + d1379 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3859 (p : Pattern) (guard : d4303 p = 1) : d701 p ≤ (0 : Int) + d1380 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d701, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3857 p hg
    simpa only [d4303, d701, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d701, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3858 p hg
    simpa only [d4303, d701, d1380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3860 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3861 (p : Pattern) (guard : d4148 p = 1) : d291 p ≤ (0 : Int) + d1296 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d291, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d291, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d291, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d4148, d291, d1296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3862 (p : Pattern) (guard : d0 p = 1) : d292 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3863 (p : Pattern) (guard : d4148 p = 1) : d293 p ≤ (0 : Int) + d1369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d293, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d293, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d293, d1369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3862 p hg
    simpa only [d4148, d293, d1369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3864 (p : Pattern) (guard : d4148 p = 1) : d294 p ≤ (0 : Int) + d1381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d294, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d294, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d294, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d294, d1381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3865 (p : Pattern) (guard : d4148 p = 1) : d295 p ≤ (0 : Int) + d1382 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d295, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d295, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d295, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d295, d1382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3866 (p : Pattern) (guard : d4148 p = 1) : d296 p ≤ (0 : Int) + d1383 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d296, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3864 p hg
    simpa only [d296, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d296, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3865 p hg
    simpa only [d296, d1383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3867 (p : Pattern) (guard : d4148 p = 1) : d297 p ≤ (0 : Int) + d1384 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d297, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3866 p hg
    simpa only [d297, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d297, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d297, d1384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3868 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3869 (p : Pattern) (guard : d4303 p = 1) : d702 p ≤ (0 : Int) + d1391 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d702, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3867 p hg
    simpa only [d4303, d702, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d702, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3868 p hg
    simpa only [d4303, d702, d1391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3870 (p : Pattern) (guard : d4303 p = 1) : d703 p ≤ (0 : Int) + d1392 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d703, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3859 p hg
    simpa only [d703, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d703, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3869 p hg
    simpa only [d703, d1392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3871 (p : Pattern) (guard : d4303 p = 1) : d704 p ≤ (0 : Int) + d1393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d704, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3869 p hg
    simpa only [d704, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d704, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d704, d1393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3872 (p : Pattern) (guard : d4303 p = 1) : d705 p ≤ (0 : Int) + d1394 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d705, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3870 p hg
    simpa only [d705, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d705, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d705, d1394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3873 (p : Pattern) (guard : d4303 p = 1) : d706 p ≤ (0 : Int) + d1395 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d706, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3845 p hg
    simpa only [d706, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d706, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3872 p hg
    simpa only [d706, d1395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3874 (p : Pattern) (guard : d4303 p = 1) : d707 p ≤ (0 : Int) + d1396 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d707, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d707, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d707, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3873 p hg
    simpa only [d707, d1396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3875 (p : Pattern) (guard : d4303 p = 1) : d708 p ≤ (0 : Int) + d1397 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d708, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3836 p hg
    simpa only [d708, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d708, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3874 p hg
    simpa only [d708, d1397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3876 (p : Pattern) (guard : d4303 p = 1) : d709 p ≤ (0 : Int) + d1398 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d709, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3827 p hg
    simpa only [d709, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d709, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3875 p hg
    simpa only [d709, d1398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3877 (p : Pattern) (guard : d4147 p = 1) : d16 p ≤ (4 : Int) + d16 p := by
  omega
theorem compare3878 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (4 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3879 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (4 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d19, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d19, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3880 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d20, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d20, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3881 (p : Pattern) (guard : d4147 p = 1) : d21 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3880 p hg
    simpa only [d4147, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3882 (p : Pattern) (guard : d4147 p = 1) : d22 p ≤ (4 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3881 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3883 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (4 : Int) + d26 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3884 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3885 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3884 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3886 (p : Pattern) (guard : d4147 p = 1) : d27 p ≤ (4 : Int) + d26 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3883 p hg
    simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3885 p hg
    simpa only [d4147, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3887 (p : Pattern) (guard : d4147 p = 1) : d28 p ≤ (4 : Int) + d4305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d28, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3881 p hg
    simpa only [d28, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d28, d4305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3886 p hg
    simpa only [d28, d4305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3888 (p : Pattern) (guard : d4147 p = 1) : d29 p ≤ (4 : Int) + d4306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d29, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3882 p hg
    simpa only [d29, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d29, d4306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3887 p hg
    simpa only [d29, d4306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3889 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (4 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3890 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (4 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d37, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d37, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3891 (p : Pattern) (guard : d4147 p = 1) : d38 p ≤ (4 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3889 p hg
    simpa only [d4147, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3890 p hg
    simpa only [d4147, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3892 (p : Pattern) (guard : d0 p = 1) : d42 p ≤ (4 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3893 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (4 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3894 (p : Pattern) (guard : d4147 p = 1) : d44 p ≤ (4 : Int) + d42 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3892 p hg
    simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3893 p hg
    simpa only [d4147, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3895 (p : Pattern) (guard : d4147 p = 1) : d45 p ≤ (4 : Int) + d4307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d45, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3891 p hg
    simpa only [d45, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d45, d4307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3894 p hg
    simpa only [d45, d4307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3896 (p : Pattern) (guard : d0 p = 1) : d46 p ≤ (4 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3897 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (4 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d43, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d43, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3898 (p : Pattern) (guard : d4147 p = 1) : d47 p ≤ (4 : Int) + d46 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3896 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3897 p hg
    simpa only [d4147, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3899 (p : Pattern) (guard : d0 p = 1) : d48 p ≤ (4 : Int) + d48 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3900 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3901 (p : Pattern) (guard : d4147 p = 1) : d49 p ≤ (4 : Int) + d48 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3900 p hg
    simpa only [d4147, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3902 (p : Pattern) (guard : d4147 p = 1) : d50 p ≤ (4 : Int) + d4308 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d50, d4308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3898 p hg
    simpa only [d50, d4308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d50, d4308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3901 p hg
    simpa only [d50, d4308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3903 (p : Pattern) (guard : d4147 p = 1) : d51 p ≤ (4 : Int) + d4309 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d51, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3895 p hg
    simpa only [d51, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d51, d4309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3902 p hg
    simpa only [d51, d4309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3904 (p : Pattern) (guard : d4147 p = 1) : d52 p ≤ (4 : Int) + d4310 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d52, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d52, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d52, d4310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3903 p hg
    simpa only [d52, d4310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3905 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (4 : Int) + d4317 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3906 (p : Pattern) (guard : d4304 p = 1) : d653 p ≤ (4 : Int) + d4318 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d653, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d4304, d653, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d653, d4318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3905 p hg
    simpa only [d4304, d653, d4318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3907 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (4 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3908 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (4 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d78, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d78, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3909 (p : Pattern) (guard : d4147 p = 1) : d79 p ≤ (4 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d4147, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3908 p hg
    simpa only [d4147, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3910 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (4 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3911 (p : Pattern) (guard : d4147 p = 1) : d63 p ≤ (4 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2683 p hg
    simpa only [d4147, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3912 (p : Pattern) (guard : d4147 p = 1) : d80 p ≤ (4 : Int) + d4312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d80, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3909 p hg
    simpa only [d80, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d80, d4312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d80, d4312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3913 (p : Pattern) (guard : d4147 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare3914 (p : Pattern) (guard : d4147 p = 1) : d81 p ≤ (4 : Int) + d4319 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d81, d4319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3912 p hg
    simpa only [d81, d4319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d81, d4319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d81, d4319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3915 (p : Pattern) (guard : d4147 p = 1) : d82 p ≤ (4 : Int) + d4320 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d82, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d82, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4147 p = 1 := by simpa only [d82, d4320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3914 p hg
    simpa only [d82, d4320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3916 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3917 (p : Pattern) (guard : d4304 p = 1) : d654 p ≤ (4 : Int) + d4322 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4304, d654, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d4304, d654, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4304, d654, d4322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3916 p hg
    simpa only [d4304, d654, d4322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3918 (p : Pattern) (guard : d4304 p = 1) : d655 p ≤ (4 : Int) + d4323 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4304 p = 1 := by simpa only [d655, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3906 p hg
    simpa only [d655, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4304 p = 1 := by simpa only [d655, d4323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d655, d4323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3919 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (4 : Int) + d4321 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
