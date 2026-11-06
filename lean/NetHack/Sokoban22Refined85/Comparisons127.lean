/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17780 (p : Pattern) (guard : d5268 p = 1) : d52 p ≤ (0 : Int) + d3351 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d52, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17728 p hg
    simpa only [d52, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d52, d3351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17694 p hg
    simpa only [d52, d3351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17781 (p : Pattern) (guard : d5268 p = 1) : d77 p ≤ (0 : Int) + d3352 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d77, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17780 p hg
    simpa only [d77, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d77, d3352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17757 p hg
    simpa only [d77, d3352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17782 (p : Pattern) (guard : d5268 p = 1) : d88 p ≤ (0 : Int) + d3353 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d88, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17781 p hg
    simpa only [d88, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d88, d3353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17741 p hg
    simpa only [d88, d3353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17783 (p : Pattern) (guard : d5268 p = 1) : d100 p ≤ (0 : Int) + d3354 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d100, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17782 p hg
    simpa only [d100, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d100, d3354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17760 p hg
    simpa only [d100, d3354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17784 (p : Pattern) (guard : d5268 p = 1) : d101 p ≤ (0 : Int) + d3355 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d101, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17779 p hg
    simpa only [d101, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d101, d3355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17783 p hg
    simpa only [d101, d3355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17785 (p : Pattern) (guard : d5268 p = 1) : d101 p ≤ (0 : Int) + d3356 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17762 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17784 p hg
    simpa only [d3356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17786 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17787 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3357 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d103, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d103, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d103, d3357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17786 p hg
    simpa only [d5268, d103, d3357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17788 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17789 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5268, d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17790 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3359 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17787 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17791 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3360 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17790 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17792 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3361 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17791 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17793 (p : Pattern) (guard : d5268 p = 1) : d104 p ≤ (0 : Int) + d3362 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d104, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d104, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d104, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d104, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17794 (p : Pattern) (guard : d5268 p = 1) : d105 p ≤ (0 : Int) + d3363 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d105, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17792 p hg
    simpa only [d105, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d105, d3363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17793 p hg
    simpa only [d105, d3363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17795 (p : Pattern) (guard : d5268 p = 1) : d105 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d105, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d105, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d105, d3364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17793 p hg
    simpa only [d105, d3364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17796 (p : Pattern) (guard : d5268 p = 1) : d105 p ≤ (0 : Int) + d3365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17794 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d3365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17797 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17798 (p : Pattern) (guard : d5268 p = 1) : d107 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5268, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5268, d107, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17799 (p : Pattern) (guard : d5268 p = 1) : d108 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d108, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d108, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d108, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d108, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17800 (p : Pattern) (guard : d5268 p = 1) : d109 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d109, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d109, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d109, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17799 p hg
    simpa only [d109, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17801 (p : Pattern) (guard : d5268 p = 1) : d110 p ≤ (0 : Int) + d3369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d110, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d110, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d110, d3369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d110, d3369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17802 (p : Pattern) (guard : d5268 p = 1) : d111 p ≤ (0 : Int) + d3370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d111, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17796 p hg
    simpa only [d111, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d111, d3370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17801 p hg
    simpa only [d111, d3370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17803 (p : Pattern) (guard : d5268 p = 1) : d112 p ≤ (0 : Int) + d3371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d112, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17709 p hg
    simpa only [d112, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d112, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d112, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17804 (p : Pattern) (guard : d5268 p = 1) : d113 p ≤ (0 : Int) + d3372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d113, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17801 p hg
    simpa only [d113, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d113, d3372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17803 p hg
    simpa only [d113, d3372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17805 (p : Pattern) (guard : d5268 p = 1) : d114 p ≤ (0 : Int) + d3373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d114, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17802 p hg
    simpa only [d114, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d114, d3373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17804 p hg
    simpa only [d114, d3373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17806 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17807 (p : Pattern) (guard : d5268 p = 1) : d116 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5268, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5268, d116, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17808 (p : Pattern) (guard : d5268 p = 1) : d117 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d117, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d117, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d117, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d117, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17809 (p : Pattern) (guard : d5268 p = 1) : d118 p ≤ (0 : Int) + d3376 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d118, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d118, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d118, d3376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17808 p hg
    simpa only [d118, d3376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17810 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17811 (p : Pattern) (guard : d5268 p = 1) : d120 p ≤ (0 : Int) + d3377 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5268, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5268, d120, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17812 (p : Pattern) (guard : d5268 p = 1) : d121 p ≤ (0 : Int) + d3378 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d121, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d121, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d121, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d121, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17813 (p : Pattern) (guard : d5268 p = 1) : d122 p ≤ (0 : Int) + d3379 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d122, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d122, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d122, d3379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17812 p hg
    simpa only [d122, d3379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17814 (p : Pattern) (guard : d5268 p = 1) : d123 p ≤ (0 : Int) + d3380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d123, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17809 p hg
    simpa only [d123, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d123, d3380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17813 p hg
    simpa only [d123, d3380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17815 (p : Pattern) (guard : d5268 p = 1) : d124 p ≤ (0 : Int) + d3381 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d124, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d124, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d124, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d124, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17816 (p : Pattern) (guard : d5268 p = 1) : d125 p ≤ (0 : Int) + d3382 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d125, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d125, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d125, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d125, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17817 (p : Pattern) (guard : d5268 p = 1) : d126 p ≤ (0 : Int) + d3383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d126, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17815 p hg
    simpa only [d126, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d126, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d126, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17818 (p : Pattern) (guard : d5268 p = 1) : d127 p ≤ (0 : Int) + d3384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d127, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17814 p hg
    simpa only [d127, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d127, d3384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17817 p hg
    simpa only [d127, d3384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17819 (p : Pattern) (guard : d5268 p = 1) : d128 p ≤ (0 : Int) + d3385 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d128, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17719 p hg
    simpa only [d128, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d128, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d128, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17820 (p : Pattern) (guard : d5268 p = 1) : d129 p ≤ (0 : Int) + d3386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d129, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17817 p hg
    simpa only [d129, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d129, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17819 p hg
    simpa only [d129, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17821 (p : Pattern) (guard : d5268 p = 1) : d130 p ≤ (0 : Int) + d3387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d130, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17818 p hg
    simpa only [d130, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d130, d3387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17820 p hg
    simpa only [d130, d3387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17822 (p : Pattern) (guard : d5268 p = 1) : d131 p ≤ (0 : Int) + d3388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d131, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17805 p hg
    simpa only [d131, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d131, d3388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17821 p hg
    simpa only [d131, d3388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17823 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17824 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3389 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d103, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5268, d103, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d103, d3389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17823 p hg
    simpa only [d5268, d103, d3389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17825 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3390 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17824 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17826 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3391 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17825 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17827 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d3392 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17826 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17828 (p : Pattern) (guard : d5268 p = 1) : d105 p ≤ (0 : Int) + d3393 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d105, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17827 p hg
    simpa only [d105, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d105, d3393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17793 p hg
    simpa only [d105, d3393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17829 (p : Pattern) (guard : d5268 p = 1) : d132 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d132, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d132, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d132, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17808 p hg
    simpa only [d132, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17830 (p : Pattern) (guard : d5268 p = 1) : d133 p ≤ (0 : Int) + d3395 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d133, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17828 p hg
    simpa only [d133, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d133, d3395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d133, d3395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17831 (p : Pattern) (guard : d5268 p = 1) : d134 p ≤ (0 : Int) + d3396 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d134, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d134, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d134, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17709 p hg
    simpa only [d134, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17832 (p : Pattern) (guard : d5268 p = 1) : d135 p ≤ (0 : Int) + d3397 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d135, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17830 p hg
    simpa only [d135, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d135, d3397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17831 p hg
    simpa only [d135, d3397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17833 (p : Pattern) (guard : d5268 p = 1) : d136 p ≤ (0 : Int) + d3398 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d136, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d136, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d136, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d136, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17834 (p : Pattern) (guard : d5268 p = 1) : d137 p ≤ (0 : Int) + d3399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d137, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17833 p hg
    simpa only [d137, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d137, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d137, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17835 (p : Pattern) (guard : d5268 p = 1) : d138 p ≤ (0 : Int) + d3400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d138, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17832 p hg
    simpa only [d138, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d138, d3400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17834 p hg
    simpa only [d138, d3400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17836 (p : Pattern) (guard : d5268 p = 1) : d139 p ≤ (0 : Int) + d3401 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d139, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d139, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d139, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d139, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17837 (p : Pattern) (guard : d5268 p = 1) : d140 p ≤ (0 : Int) + d3402 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d140, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17813 p hg
    simpa only [d140, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d140, d3402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17836 p hg
    simpa only [d140, d3402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17838 (p : Pattern) (guard : d5268 p = 1) : d141 p ≤ (0 : Int) + d3403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d141, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d141, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d141, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17719 p hg
    simpa only [d141, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17839 (p : Pattern) (guard : d5268 p = 1) : d142 p ≤ (0 : Int) + d3404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d142, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17837 p hg
    simpa only [d142, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d142, d3404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17838 p hg
    simpa only [d142, d3404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17840 (p : Pattern) (guard : d5268 p = 1) : d143 p ≤ (0 : Int) + d3405 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d143, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d143, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d143, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17721 p hg
    simpa only [d143, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17841 (p : Pattern) (guard : d5268 p = 1) : d144 p ≤ (0 : Int) + d3406 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d144, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17840 p hg
    simpa only [d144, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d144, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d144, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17842 (p : Pattern) (guard : d5268 p = 1) : d145 p ≤ (0 : Int) + d3407 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d145, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17839 p hg
    simpa only [d145, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d145, d3407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17841 p hg
    simpa only [d145, d3407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17843 (p : Pattern) (guard : d5268 p = 1) : d146 p ≤ (0 : Int) + d3408 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d146, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17835 p hg
    simpa only [d146, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d146, d3408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17842 p hg
    simpa only [d146, d3408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17844 (p : Pattern) (guard : d5268 p = 1) : d147 p ≤ (0 : Int) + d3409 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d147, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17822 p hg
    simpa only [d147, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d147, d3409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17843 p hg
    simpa only [d147, d3409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17845 (p : Pattern) (guard : d5268 p = 1) : d111 p ≤ (0 : Int) + d3410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d111, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d111, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d111, d3410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17801 p hg
    simpa only [d111, d3410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17846 (p : Pattern) (guard : d5268 p = 1) : d114 p ≤ (0 : Int) + d3411 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d114, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17845 p hg
    simpa only [d114, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d114, d3411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17804 p hg
    simpa only [d114, d3411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17847 (p : Pattern) (guard : d5268 p = 1) : d148 p ≤ (0 : Int) + d3412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d148, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d148, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d148, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17812 p hg
    simpa only [d148, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17848 (p : Pattern) (guard : d5268 p = 1) : d149 p ≤ (0 : Int) + d3413 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d149, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d149, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d149, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17847 p hg
    simpa only [d149, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17849 (p : Pattern) (guard : d5268 p = 1) : d150 p ≤ (0 : Int) + d3414 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d150, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17848 p hg
    simpa only [d150, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d150, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d150, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17850 (p : Pattern) (guard : d5268 p = 1) : d151 p ≤ (0 : Int) + d3415 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d151, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17849 p hg
    simpa only [d151, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d151, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d151, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17851 (p : Pattern) (guard : d5268 p = 1) : d152 p ≤ (0 : Int) + d3416 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d152, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17846 p hg
    simpa only [d152, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d152, d3416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17850 p hg
    simpa only [d152, d3416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17852 (p : Pattern) (guard : d5268 p = 1) : d133 p ≤ (0 : Int) + d3417 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d133, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d133, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d133, d3417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d133, d3417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17853 (p : Pattern) (guard : d5268 p = 1) : d135 p ≤ (0 : Int) + d3418 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d135, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17852 p hg
    simpa only [d135, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d135, d3418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17831 p hg
    simpa only [d135, d3418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17854 (p : Pattern) (guard : d5268 p = 1) : d138 p ≤ (0 : Int) + d3419 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d138, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17853 p hg
    simpa only [d138, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d138, d3419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17834 p hg
    simpa only [d138, d3419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17855 (p : Pattern) (guard : d5268 p = 1) : d153 p ≤ (0 : Int) + d3420 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d153, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17847 p hg
    simpa only [d153, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d153, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d153, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17856 (p : Pattern) (guard : d5268 p = 1) : d154 p ≤ (0 : Int) + d3421 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d154, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17855 p hg
    simpa only [d154, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d154, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d154, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17857 (p : Pattern) (guard : d5268 p = 1) : d155 p ≤ (0 : Int) + d3422 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d155, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17856 p hg
    simpa only [d155, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d155, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d155, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17858 (p : Pattern) (guard : d5268 p = 1) : d156 p ≤ (0 : Int) + d3423 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d156, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17854 p hg
    simpa only [d156, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d156, d3423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17857 p hg
    simpa only [d156, d3423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17859 (p : Pattern) (guard : d5268 p = 1) : d157 p ≤ (0 : Int) + d3424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d157, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17851 p hg
    simpa only [d157, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d157, d3424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17858 p hg
    simpa only [d157, d3424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17860 (p : Pattern) (guard : d5268 p = 1) : d158 p ≤ (0 : Int) + d3425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d158, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17844 p hg
    simpa only [d158, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d158, d3425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17859 p hg
    simpa only [d158, d3425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17861 (p : Pattern) (guard : d5268 p = 1) : d159 p ≤ (0 : Int) + d3426 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d159, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17803 p hg
    simpa only [d159, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d159, d3426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d159, d3426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17862 (p : Pattern) (guard : d5268 p = 1) : d160 p ≤ (0 : Int) + d3427 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d160, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17861 p hg
    simpa only [d160, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d160, d3427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d160, d3427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17863 (p : Pattern) (guard : d5268 p = 1) : d161 p ≤ (0 : Int) + d3428 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d161, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17862 p hg
    simpa only [d161, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d161, d3428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d161, d3428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17864 (p : Pattern) (guard : d5268 p = 1) : d162 p ≤ (0 : Int) + d3429 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d162, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17863 p hg
    simpa only [d162, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d162, d3429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d162, d3429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17865 (p : Pattern) (guard : d5268 p = 1) : d163 p ≤ (0 : Int) + d3430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d163, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17859 p hg
    simpa only [d163, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d163, d3430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17864 p hg
    simpa only [d163, d3430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17866 (p : Pattern) (guard : d5268 p = 1) : d164 p ≤ (0 : Int) + d3431 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d164, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17860 p hg
    simpa only [d164, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d164, d3431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17865 p hg
    simpa only [d164, d3431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17867 (p : Pattern) (guard : d5268 p = 1) : d131 p ≤ (0 : Int) + d3432 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d131, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17846 p hg
    simpa only [d131, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d131, d3432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17821 p hg
    simpa only [d131, d3432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17868 (p : Pattern) (guard : d5268 p = 1) : d146 p ≤ (0 : Int) + d3433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d146, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17854 p hg
    simpa only [d146, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d146, d3433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17842 p hg
    simpa only [d146, d3433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17869 (p : Pattern) (guard : d5268 p = 1) : d147 p ≤ (0 : Int) + d3434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d147, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d147, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d147, d3434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d147, d3434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17870 (p : Pattern) (guard : d5268 p = 1) : d158 p ≤ (0 : Int) + d3435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d158, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d158, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d158, d3435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17859 p hg
    simpa only [d158, d3435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17871 (p : Pattern) (guard : d5268 p = 1) : d165 p ≤ (0 : Int) + d3436 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d165, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17859 p hg
    simpa only [d165, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d165, d3436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d165, d3436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17872 (p : Pattern) (guard : d5268 p = 1) : d166 p ≤ (0 : Int) + d3437 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d166, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d166, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d166, d3437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d166, d3437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17873 (p : Pattern) (guard : d5268 p = 1) : d167 p ≤ (0 : Int) + d3438 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d167, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17866 p hg
    simpa only [d167, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d167, d3438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d167, d3438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17874 (p : Pattern) (guard : d5268 p = 1) : d168 p ≤ (0 : Int) + d3439 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d168, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17762 p hg
    simpa only [d168, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d168, d3439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d168, d3439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17875 (p : Pattern) (guard : d5268 p = 1) : d169 p ≤ (0 : Int) + d3440 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d169, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17785 p hg
    simpa only [d169, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d169, d3440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d169, d3440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17876 (p : Pattern) (guard : d5268 p = 1) : d170 p ≤ (0 : Int) + d3441 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d170, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d170, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d170, d3441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17679 p hg
    simpa only [d170, d3441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17877 (p : Pattern) (guard : d5268 p = 1) : d171 p ≤ (0 : Int) + d3442 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d171, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d171, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d171, d3442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d171, d3442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17878 (p : Pattern) (guard : d5268 p = 1) : d172 p ≤ (0 : Int) + d3443 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d172, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17674 p hg
    simpa only [d172, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d172, d3443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17684 p hg
    simpa only [d172, d3443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17879 (p : Pattern) (guard : d5268 p = 1) : d173 p ≤ (0 : Int) + d3444 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d173, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17678 p hg
    simpa only [d173, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d173, d3444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d173, d3444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17880 (p : Pattern) (guard : d5268 p = 1) : d174 p ≤ (0 : Int) + d3445 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d174, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d174, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d174, d3445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17879 p hg
    simpa only [d174, d3445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17881 (p : Pattern) (guard : d5268 p = 1) : d175 p ≤ (0 : Int) + d3446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d175, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17877 p hg
    simpa only [d175, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d175, d3446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17880 p hg
    simpa only [d175, d3446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17882 (p : Pattern) (guard : d5268 p = 1) : d176 p ≤ (0 : Int) + d3447 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d176, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17715 p hg
    simpa only [d176, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d176, d3447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17879 p hg
    simpa only [d176, d3447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17883 (p : Pattern) (guard : d5268 p = 1) : d177 p ≤ (0 : Int) + d3448 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d177, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17882 p hg
    simpa only [d177, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d177, d3448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17722 p hg
    simpa only [d177, d3448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17884 (p : Pattern) (guard : d5268 p = 1) : d178 p ≤ (0 : Int) + d3449 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d178, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d178, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d178, d3449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d178, d3449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17885 (p : Pattern) (guard : d5268 p = 1) : d179 p ≤ (0 : Int) + d3450 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d179, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17728 p hg
    simpa only [d179, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d179, d3450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17884 p hg
    simpa only [d179, d3450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17886 (p : Pattern) (guard : d5268 p = 1) : d180 p ≤ (0 : Int) + d3451 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d180, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d180, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d180, d3451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17686 p hg
    simpa only [d180, d3451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17887 (p : Pattern) (guard : d5268 p = 1) : d181 p ≤ (0 : Int) + d3452 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d181, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17879 p hg
    simpa only [d181, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d181, d3452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17721 p hg
    simpa only [d181, d3452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17888 (p : Pattern) (guard : d5268 p = 1) : d182 p ≤ (0 : Int) + d3453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d182, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17886 p hg
    simpa only [d182, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d182, d3453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17887 p hg
    simpa only [d182, d3453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17889 (p : Pattern) (guard : d5268 p = 1) : d183 p ≤ (0 : Int) + d3454 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d183, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17879 p hg
    simpa only [d183, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d183, d3454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d183, d3454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17890 (p : Pattern) (guard : d5268 p = 1) : d184 p ≤ (0 : Int) + d3455 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d184, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d184, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d184, d3455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d184, d3455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17891 (p : Pattern) (guard : d5268 p = 1) : d185 p ≤ (0 : Int) + d3456 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d185, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17888 p hg
    simpa only [d185, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d185, d3456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17890 p hg
    simpa only [d185, d3456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17892 (p : Pattern) (guard : d5268 p = 1) : d186 p ≤ (0 : Int) + d3457 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d186, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17736 p hg
    simpa only [d186, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d186, d3457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17891 p hg
    simpa only [d186, d3457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17893 (p : Pattern) (guard : d5268 p = 1) : d187 p ≤ (0 : Int) + d3458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d187, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17885 p hg
    simpa only [d187, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d187, d3458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17892 p hg
    simpa only [d187, d3458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17894 (p : Pattern) (guard : d5268 p = 1) : d188 p ≤ (0 : Int) + d3459 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d188, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17659 p hg
    simpa only [d188, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d188, d3459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17730 p hg
    simpa only [d188, d3459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17895 (p : Pattern) (guard : d5268 p = 1) : d189 p ≤ (0 : Int) + d3460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d189, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17894 p hg
    simpa only [d189, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d189, d3460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17731 p hg
    simpa only [d189, d3460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17896 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17897 (p : Pattern) (guard : d5268 p = 1) : d191 p ≤ (0 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d5268, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5268, d191, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17898 (p : Pattern) (guard : d5268 p = 1) : d192 p ≤ (0 : Int) + d3462 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d192, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d192, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d192, d3462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d192, d3462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17899 (p : Pattern) (guard : d5268 p = 1) : d193 p ≤ (0 : Int) + d3463 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d193, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d193, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d193, d3463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17898 p hg
    simpa only [d193, d3463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17900 (p : Pattern) (guard : d5268 p = 1) : d194 p ≤ (0 : Int) + d3464 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d194, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d194, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d194, d3464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17899 p hg
    simpa only [d194, d3464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17901 (p : Pattern) (guard : d5268 p = 1) : d195 p ≤ (0 : Int) + d3465 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d195, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17900 p hg
    simpa only [d195, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d195, d3465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d195, d3465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17902 (p : Pattern) (guard : d5268 p = 1) : d196 p ≤ (0 : Int) + d3466 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d196, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17901 p hg
    simpa only [d196, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d196, d3466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d196, d3466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17903 (p : Pattern) (guard : d5268 p = 1) : d197 p ≤ (0 : Int) + d3467 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d197, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17895 p hg
    simpa only [d197, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d197, d3467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17902 p hg
    simpa only [d197, d3467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17904 (p : Pattern) (guard : d5268 p = 1) : d198 p ≤ (0 : Int) + d3468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d198, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17663 p hg
    simpa only [d198, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d198, d3468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17711 p hg
    simpa only [d198, d3468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17905 (p : Pattern) (guard : d5268 p = 1) : d199 p ≤ (0 : Int) + d3469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d199, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17702 p hg
    simpa only [d199, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d199, d3469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17904 p hg
    simpa only [d199, d3469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17906 (p : Pattern) (guard : d5268 p = 1) : d200 p ≤ (0 : Int) + d3470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d200, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17905 p hg
    simpa only [d200, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d200, d3470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17738 p hg
    simpa only [d200, d3470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17907 (p : Pattern) (guard : d5268 p = 1) : d201 p ≤ (0 : Int) + d3471 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d201, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17899 p hg
    simpa only [d201, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d201, d3471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d201, d3471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17908 (p : Pattern) (guard : d5268 p = 1) : d202 p ≤ (0 : Int) + d3472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d202, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d202, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d202, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d202, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17909 (p : Pattern) (guard : d5268 p = 1) : d203 p ≤ (0 : Int) + d3473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d203, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17908 p hg
    simpa only [d203, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d203, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d203, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17910 (p : Pattern) (guard : d5268 p = 1) : d204 p ≤ (0 : Int) + d3474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d204, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d204, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d204, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d204, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17911 (p : Pattern) (guard : d5268 p = 1) : d205 p ≤ (0 : Int) + d3475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d205, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17903 p hg
    simpa only [d205, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d205, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17910 p hg
    simpa only [d205, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17912 (p : Pattern) (guard : d5268 p = 1) : d206 p ≤ (0 : Int) + d3476 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d206, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d206, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d206, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17911 p hg
    simpa only [d206, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17913 (p : Pattern) (guard : d5268 p = 1) : d207 p ≤ (0 : Int) + d3477 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d207, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17911 p hg
    simpa only [d207, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d207, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d207, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17914 (p : Pattern) (guard : d5268 p = 1) : d208 p ≤ (0 : Int) + d3478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d208, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17912 p hg
    simpa only [d208, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d208, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17913 p hg
    simpa only [d208, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17915 (p : Pattern) (guard : d5268 p = 1) : d209 p ≤ (0 : Int) + d3479 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d209, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17779 p hg
    simpa only [d209, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d209, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17914 p hg
    simpa only [d209, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17916 (p : Pattern) (guard : d5268 p = 1) : d210 p ≤ (0 : Int) + d3480 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d210, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17762 p hg
    simpa only [d210, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d210, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17915 p hg
    simpa only [d210, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17917 (p : Pattern) (guard : d5268 p = 1) : d211 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d211, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d211, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d211, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d211, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17918 (p : Pattern) (guard : d5268 p = 1) : d212 p ≤ (0 : Int) + d3482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d212, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17830 p hg
    simpa only [d212, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d212, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17917 p hg
    simpa only [d212, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17919 (p : Pattern) (guard : d5268 p = 1) : d213 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d213, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17917 p hg
    simpa only [d213, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d213, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d213, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
