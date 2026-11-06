/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons269
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37800 (p : Pattern) (guard : d8111 p = 1) : d3609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37626 p hg
    simpa only [d8111, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37801 (p : Pattern) (guard : d8117 p = 1) : d3610 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37800 p hg
    simpa only [d8117, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37613 p hg
    simpa only [d8117, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37802 (p : Pattern) (guard : d0 p = 1) : d3612 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37803 (p : Pattern) (guard : d8123 p = 1) : d3613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37801 p hg
    simpa only [d8123, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37802 p hg
    simpa only [d8123, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37804 (p : Pattern) (guard : d8124 p = 1) : d3614 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37799 p hg
    simpa only [d8124, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37803 p hg
    simpa only [d8124, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37805 (p : Pattern) (guard : d8125 p = 1) : d3709 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37793 p hg
    simpa only [d8125, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37804 p hg
    simpa only [d8125, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37806 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37807 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37806 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37808 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37807 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37809 (p : Pattern) (guard : d8100 p = 1) : d3552 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37808 p hg
    simpa only [d8100, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37559 p hg
    simpa only [d8100, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37810 (p : Pattern) (guard : d8106 p = 1) : d3553 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37809 p hg
    simpa only [d8106, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37775 p hg
    simpa only [d8106, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37811 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d5843, d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37812 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37811 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37813 (p : Pattern) (guard : d5854 p = 1) : d30 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37812 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37814 (p : Pattern) (guard : d8099 p = 1) : d30 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37813 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37815 (p : Pattern) (guard : d0 p = 1) : d3622 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37816 (p : Pattern) (guard : d8105 p = 1) : d3623 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37814 p hg
    simpa only [d8105, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37815 p hg
    simpa only [d8105, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37817 (p : Pattern) (guard : d0 p = 1) : d3627 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37818 (p : Pattern) (guard : d8111 p = 1) : d3628 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d8111, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d8111, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37819 (p : Pattern) (guard : d8112 p = 1) : d3710 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37810 p hg
    simpa only [d8112, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d8112, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37820 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d5843, d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d17, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37821 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37822 (p : Pattern) (guard : d5854 p = 1) : d17 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37823 (p : Pattern) (guard : d8099 p = 1) : d17 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37824 (p : Pattern) (guard : d8105 p = 1) : d3558 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d8105, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37780 p hg
    simpa only [d8105, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37825 (p : Pattern) (guard : d8111 p = 1) : d3563 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d8111, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37782 p hg
    simpa only [d8111, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37826 (p : Pattern) (guard : d0 p = 1) : d3573 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37827 (p : Pattern) (guard : d8117 p = 1) : d3630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37825 p hg
    simpa only [d8117, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d8117, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37828 (p : Pattern) (guard : d8118 p = 1) : d3711 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d8118, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37827 p hg
    simpa only [d8118, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37829 (p : Pattern) (guard : d8117 p = 1) : d3637 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37783 p hg
    simpa only [d8117, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37830 (p : Pattern) (guard : d8123 p = 1) : d3641 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37829 p hg
    simpa only [d8123, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d8123, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37831 (p : Pattern) (guard : d8124 p = 1) : d3712 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37828 p hg
    simpa only [d8124, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d8124, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37832 (p : Pattern) (guard : d8111 p = 1) : d3595 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37658 p hg
    simpa only [d8111, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d8111, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37833 (p : Pattern) (guard : d0 p = 1) : d3644 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37834 (p : Pattern) (guard : d8117 p = 1) : d3645 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d8117, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37833 p hg
    simpa only [d8117, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37835 (p : Pattern) (guard : d0 p = 1) : d3646 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37836 (p : Pattern) (guard : d8123 p = 1) : d3647 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37834 p hg
    simpa only [d8123, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d8123, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37837 (p : Pattern) (guard : d0 p = 1) : d3652 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37838 (p : Pattern) (guard : d8129 p = 1) : d3653 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37836 p hg
    simpa only [d8129, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d8129, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37839 (p : Pattern) (guard : d8130 p = 1) : d3713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d8130, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37838 p hg
    simpa only [d8130, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37840 (p : Pattern) (guard : d8131 p = 1) : d3714 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37805 p hg
    simpa only [d8131, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d8131, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37841 (p : Pattern) (guard : d0 p = 1) : d3664 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37842 (p : Pattern) (guard : d8111 p = 1) : d3665 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37658 p hg
    simpa only [d8111, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d8111, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37843 (p : Pattern) (guard : d8112 p = 1) : d3666 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37564 p hg
    simpa only [d8112, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37842 p hg
    simpa only [d8112, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37844 (p : Pattern) (guard : d0 p = 1) : d3670 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37845 (p : Pattern) (guard : d8117 p = 1) : d3671 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37628 p hg
    simpa only [d8117, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d8117, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37846 (p : Pattern) (guard : d8118 p = 1) : d3672 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37843 p hg
    simpa only [d8118, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37845 p hg
    simpa only [d8118, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37847 (p : Pattern) (guard : d0 p = 1) : d3675 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37848 (p : Pattern) (guard : d8123 p = 1) : d3676 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37845 p hg
    simpa only [d8123, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37847 p hg
    simpa only [d8123, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37849 (p : Pattern) (guard : d8124 p = 1) : d3677 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d8124, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37848 p hg
    simpa only [d8124, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37850 (p : Pattern) (guard : d8129 p = 1) : d3683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37633 p hg
    simpa only [d8129, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37851 (p : Pattern) (guard : d8130 p = 1) : d3684 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37849 p hg
    simpa only [d8130, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37850 p hg
    simpa only [d8130, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37852 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d5843, d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37853 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37854 (p : Pattern) (guard : d5854 p = 1) : d13 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37853 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37855 (p : Pattern) (guard : d8099 p = 1) : d13 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37854 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37856 (p : Pattern) (guard : d8105 p = 1) : d3582 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37855 p hg
    simpa only [d8105, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37625 p hg
    simpa only [d8105, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37857 (p : Pattern) (guard : d8111 p = 1) : d3665 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d8111, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d8111, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37858 (p : Pattern) (guard : d8117 p = 1) : d3685 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37857 p hg
    simpa only [d8117, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37642 p hg
    simpa only [d8117, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37859 (p : Pattern) (guard : d0 p = 1) : d3686 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37860 (p : Pattern) (guard : d8123 p = 1) : d3687 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37858 p hg
    simpa only [d8123, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37859 p hg
    simpa only [d8123, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37861 (p : Pattern) (guard : d0 p = 1) : d3689 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37862 (p : Pattern) (guard : d8129 p = 1) : d3690 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37860 p hg
    simpa only [d8129, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37861 p hg
    simpa only [d8129, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37863 (p : Pattern) (guard : d0 p = 1) : d3693 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37864 (p : Pattern) (guard : d8135 p = 1) : d3694 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37862 p hg
    simpa only [d8135, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37863 p hg
    simpa only [d8135, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37865 (p : Pattern) (guard : d8136 p = 1) : d3695 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37851 p hg
    simpa only [d8136, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37864 p hg
    simpa only [d8136, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37866 (p : Pattern) (guard : d8137 p = 1) : d3715 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37840 p hg
    simpa only [d8137, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37865 p hg
    simpa only [d8137, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37867 (p : Pattern) (guard : d8112 p = 1) : d3666 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37561 p hg
    simpa only [d8112, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37857 p hg
    simpa only [d8112, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37868 (p : Pattern) (guard : d8117 p = 1) : d3671 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37659 p hg
    simpa only [d8117, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d8117, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37869 (p : Pattern) (guard : d8118 p = 1) : d3672 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37867 p hg
    simpa only [d8118, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37868 p hg
    simpa only [d8118, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37870 (p : Pattern) (guard : d8124 p = 1) : d3677 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d8124, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37848 p hg
    simpa only [d8124, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37871 (p : Pattern) (guard : d8130 p = 1) : d3684 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d8130, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37850 p hg
    simpa only [d8130, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37872 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d5843, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37873 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37874 (p : Pattern) (guard : d5854 p = 1) : d13 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37873 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37875 (p : Pattern) (guard : d8099 p = 1) : d13 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37874 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37876 (p : Pattern) (guard : d8105 p = 1) : d3582 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37875 p hg
    simpa only [d8105, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37625 p hg
    simpa only [d8105, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37877 (p : Pattern) (guard : d8111 p = 1) : d3665 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37876 p hg
    simpa only [d8111, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d8111, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37878 (p : Pattern) (guard : d8117 p = 1) : d3685 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37877 p hg
    simpa only [d8117, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37642 p hg
    simpa only [d8117, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37879 (p : Pattern) (guard : d8123 p = 1) : d3687 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37878 p hg
    simpa only [d8123, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37859 p hg
    simpa only [d8123, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37880 (p : Pattern) (guard : d8129 p = 1) : d3690 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37879 p hg
    simpa only [d8129, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37861 p hg
    simpa only [d8129, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37881 (p : Pattern) (guard : d8135 p = 1) : d3694 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37880 p hg
    simpa only [d8135, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37863 p hg
    simpa only [d8135, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37882 (p : Pattern) (guard : d8136 p = 1) : d3695 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37871 p hg
    simpa only [d8136, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37881 p hg
    simpa only [d8136, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37883 (p : Pattern) (guard : d8142 p = 1) : d3716 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37882 p hg
    simpa only [d8142, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37884 (p : Pattern) (guard : d8143 p = 1) : d3717 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37866 p hg
    simpa only [d8143, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37883 p hg
    simpa only [d8143, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37885 (p : Pattern) (guard : d8144 p = 1) : d3718 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37771 p hg
    simpa only [d8144, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37884 p hg
    simpa only [d8144, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37886 (p : Pattern) (guard : d8085 p = 1) : d3734 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36978 p hg
    simpa only [d8085, d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37146 p hg
    simpa only [d8085, d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37887 (p : Pattern) (guard : d8090 p = 1) : d3735 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37886 p hg
    simpa only [d8090, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37202 p hg
    simpa only [d8090, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37888 (p : Pattern) (guard : d8089 p = 1) : d3737 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37146 p hg
    simpa only [d8089, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d8089, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37889 (p : Pattern) (guard : d8094 p = 1) : d3738 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37888 p hg
    simpa only [d8094, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37007 p hg
    simpa only [d8094, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37890 (p : Pattern) (guard : d8095 p = 1) : d3739 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37887 p hg
    simpa only [d8095, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37889 p hg
    simpa only [d8095, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37891 (p : Pattern) (guard : d8089 p = 1) : d3741 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37201 p hg
    simpa only [d8089, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d8089, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37892 (p : Pattern) (guard : d8094 p = 1) : d3742 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37891 p hg
    simpa only [d8094, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37011 p hg
    simpa only [d8094, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37893 (p : Pattern) (guard : d8100 p = 1) : d3743 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37892 p hg
    simpa only [d8100, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37894 (p : Pattern) (guard : d8101 p = 1) : d3744 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37890 p hg
    simpa only [d8101, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37893 p hg
    simpa only [d8101, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37895 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36999 p hg
    simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37896 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37895 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37897 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37896 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37366 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37898 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37897 p hg
    simpa only [d8100, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37899 (p : Pattern) (guard : d5854 p = 1) : d3741 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37365 p hg
    simpa only [d5854, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5854, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37900 (p : Pattern) (guard : d8099 p = 1) : d3742 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d8099, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d8099, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37901 (p : Pattern) (guard : d8105 p = 1) : d3743 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d8105, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37902 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d8106, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d8106, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37903 (p : Pattern) (guard : d8107 p = 1) : d3747 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37894 p hg
    simpa only [d8107, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d8107, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37904 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37905 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37906 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37905 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37907 (p : Pattern) (guard : d8100 p = 1) : d3745 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d8100, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37275 p hg
    simpa only [d8100, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37908 (p : Pattern) (guard : d8106 p = 1) : d3746 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37907 p hg
    simpa only [d8106, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37279 p hg
    simpa only [d8106, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37909 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d5843, d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37910 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37909 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37911 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37912 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37913 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d8105, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37914 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37913 p hg
    simpa only [d8111, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37915 (p : Pattern) (guard : d8112 p = 1) : d3757 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37908 p hg
    simpa only [d8112, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37914 p hg
    simpa only [d8112, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37916 (p : Pattern) (guard : d8113 p = 1) : d3758 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d8113, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d8113, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37917 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d5843, d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37918 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37919 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37918 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37920 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37921 (p : Pattern) (guard : d8105 p = 1) : d3751 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37920 p hg
    simpa only [d8105, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37284 p hg
    simpa only [d8105, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37922 (p : Pattern) (guard : d8111 p = 1) : d3756 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d8111, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37286 p hg
    simpa only [d8111, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37923 (p : Pattern) (guard : d8112 p = 1) : d3757 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37315 p hg
    simpa only [d8112, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37922 p hg
    simpa only [d8112, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37924 (p : Pattern) (guard : d8117 p = 1) : d3759 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37135 p hg
    simpa only [d8117, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37925 (p : Pattern) (guard : d8118 p = 1) : d3760 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37923 p hg
    simpa only [d8118, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d8118, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37926 (p : Pattern) (guard : d8119 p = 1) : d3761 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37916 p hg
    simpa only [d8119, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37925 p hg
    simpa only [d8119, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37927 (p : Pattern) (guard : d8106 p = 1) : d3773 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37247 p hg
    simpa only [d8106, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37189 p hg
    simpa only [d8106, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37928 (p : Pattern) (guard : d8111 p = 1) : d3779 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37390 p hg
    simpa only [d8111, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37195 p hg
    simpa only [d8111, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37929 (p : Pattern) (guard : d8112 p = 1) : d3780 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37927 p hg
    simpa only [d8112, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37928 p hg
    simpa only [d8112, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37930 (p : Pattern) (guard : d8111 p = 1) : d3781 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37368 p hg
    simpa only [d8111, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37931 (p : Pattern) (guard : d8117 p = 1) : d3788 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37930 p hg
    simpa only [d8117, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37304 p hg
    simpa only [d8117, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37932 (p : Pattern) (guard : d8118 p = 1) : d3789 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37929 p hg
    simpa only [d8118, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37931 p hg
    simpa only [d8118, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37933 (p : Pattern) (guard : d8124 p = 1) : d3792 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d8124, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37308 p hg
    simpa only [d8124, d3792, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37934 (p : Pattern) (guard : d8125 p = 1) : d3793 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d8125, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37933 p hg
    simpa only [d8125, d3793, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37935 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35744 p hg
    simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37936 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37935 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37365 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37937 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37388 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37938 (p : Pattern) (guard : d5854 p = 1) : d3737 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37365 p hg
    simpa only [d5854, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5854, d3737, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37939 (p : Pattern) (guard : d8099 p = 1) : d3738 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37938 p hg
    simpa only [d8099, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d8099, d3738, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
