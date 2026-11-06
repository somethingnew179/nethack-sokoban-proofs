/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons226
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31780 (p : Pattern) (guard : d5849 p = 1) : d3754 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3754, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31779 p hg
    simpa only [d5849, d3754, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3754, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d5849, d3754, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31781 (p : Pattern) (guard : d5849 p = 1) : d3755 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3755, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31780 p hg
    simpa only [d3755, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3755, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3755, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31782 (p : Pattern) (guard : d5849 p = 1) : d3756 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3756, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31776 p hg
    simpa only [d3756, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3756, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31781 p hg
    simpa only [d3756, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31783 (p : Pattern) (guard : d5849 p = 1) : d3757 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3757, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31768 p hg
    simpa only [d3757, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3757, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31782 p hg
    simpa only [d3757, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31784 (p : Pattern) (guard : d5849 p = 1) : d3758 p ≤ (0 : Int) + d2332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3758, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31765 p hg
    simpa only [d3758, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3758, d2332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31783 p hg
    simpa only [d3758, d2332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31785 (p : Pattern) (guard : d5849 p = 1) : d3759 p ≤ (0 : Int) + d2333 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3759, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3759, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3759, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3759, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31786 (p : Pattern) (guard : d5849 p = 1) : d3760 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3760, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31783 p hg
    simpa only [d3760, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3760, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31785 p hg
    simpa only [d3760, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31787 (p : Pattern) (guard : d5849 p = 1) : d3761 p ≤ (0 : Int) + d2335 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3761, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31784 p hg
    simpa only [d3761, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3761, d2335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31786 p hg
    simpa only [d3761, d2335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31788 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31789 (p : Pattern) (guard : d5847 p = 1) : d3762 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3762, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3762, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3762, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31788 p hg
    simpa only [d5847, d3762, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31790 (p : Pattern) (guard : d5848 p = 1) : d3763 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31789 p hg
    simpa only [d5848, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31791 (p : Pattern) (guard : d0 p = 1) : d3764 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31792 (p : Pattern) (guard : d5849 p = 1) : d3765 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3765, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31790 p hg
    simpa only [d5849, d3765, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3765, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31791 p hg
    simpa only [d5849, d3765, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31793 (p : Pattern) (guard : d5849 p = 1) : d3766 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31766 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31792 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31794 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31795 (p : Pattern) (guard : d5847 p = 1) : d3767 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3767, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3767, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3767, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31794 p hg
    simpa only [d5847, d3767, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31796 (p : Pattern) (guard : d5848 p = 1) : d3768 p ≤ (0 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31795 p hg
    simpa only [d5848, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31797 (p : Pattern) (guard : d0 p = 1) : d3770 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31798 (p : Pattern) (guard : d5849 p = 1) : d3771 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3771, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31796 p hg
    simpa only [d5849, d3771, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3771, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31797 p hg
    simpa only [d5849, d3771, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31799 (p : Pattern) (guard : d5849 p = 1) : d3772 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3772, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31798 p hg
    simpa only [d3772, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3772, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3772, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31800 (p : Pattern) (guard : d5849 p = 1) : d3773 p ≤ (0 : Int) + d2338 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3773, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d3773, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3773, d2338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31799 p hg
    simpa only [d3773, d2338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31801 (p : Pattern) (guard : d5847 p = 1) : d317 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d317, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d5847, d317, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d317, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d317, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31802 (p : Pattern) (guard : d5848 p = 1) : d3774 p ≤ (0 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31801 p hg
    simpa only [d5848, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31803 (p : Pattern) (guard : d0 p = 1) : d3776 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31804 (p : Pattern) (guard : d5849 p = 1) : d3777 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3777, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31802 p hg
    simpa only [d5849, d3777, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3777, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31803 p hg
    simpa only [d5849, d3777, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31805 (p : Pattern) (guard : d5849 p = 1) : d3778 p ≤ (0 : Int) + d2340 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3778, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31804 p hg
    simpa only [d3778, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3778, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3778, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31806 (p : Pattern) (guard : d5849 p = 1) : d3779 p ≤ (0 : Int) + d2341 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3779, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d3779, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3779, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31805 p hg
    simpa only [d3779, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31807 (p : Pattern) (guard : d5849 p = 1) : d3780 p ≤ (0 : Int) + d2342 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3780, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31800 p hg
    simpa only [d3780, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3780, d2342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31806 p hg
    simpa only [d3780, d2342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31808 (p : Pattern) (guard : d5849 p = 1) : d3781 p ≤ (0 : Int) + d2343 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3781, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d3781, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3781, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3781, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31809 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31810 (p : Pattern) (guard : d5847 p = 1) : d3782 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3782, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3782, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3782, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31809 p hg
    simpa only [d5847, d3782, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31811 (p : Pattern) (guard : d5848 p = 1) : d3783 p ≤ (0 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31810 p hg
    simpa only [d5848, d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31812 (p : Pattern) (guard : d0 p = 1) : d3784 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31813 (p : Pattern) (guard : d5849 p = 1) : d3785 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3785, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31811 p hg
    simpa only [d5849, d3785, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3785, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31812 p hg
    simpa only [d5849, d3785, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31814 (p : Pattern) (guard : d5849 p = 1) : d3786 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31771 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31813 p hg
    simpa only [d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31815 (p : Pattern) (guard : d5849 p = 1) : d3787 p ≤ (0 : Int) + d2344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3787, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31814 p hg
    simpa only [d3787, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3787, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3787, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31816 (p : Pattern) (guard : d5849 p = 1) : d3788 p ≤ (0 : Int) + d2345 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3788, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31808 p hg
    simpa only [d3788, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3788, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d3788, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31817 (p : Pattern) (guard : d5849 p = 1) : d3789 p ≤ (0 : Int) + d2346 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3789, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31807 p hg
    simpa only [d3789, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3789, d2346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31816 p hg
    simpa only [d3789, d2346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31818 (p : Pattern) (guard : d5849 p = 1) : d3790 p ≤ (0 : Int) + d2347 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3790, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31638 p hg
    simpa only [d3790, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3790, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3790, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31819 (p : Pattern) (guard : d5849 p = 1) : d3791 p ≤ (0 : Int) + d2348 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3791, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31816 p hg
    simpa only [d3791, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3791, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31818 p hg
    simpa only [d3791, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31820 (p : Pattern) (guard : d5849 p = 1) : d3792 p ≤ (0 : Int) + d2349 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3792, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31817 p hg
    simpa only [d3792, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3792, d2349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31819 p hg
    simpa only [d3792, d2349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31821 (p : Pattern) (guard : d5849 p = 1) : d3793 p ≤ (0 : Int) + d2350 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3793, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31787 p hg
    simpa only [d3793, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3793, d2350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31820 p hg
    simpa only [d3793, d2350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31822 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31823 (p : Pattern) (guard : d5849 p = 1) : d102 p ≤ (0 : Int) + d2351 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31760 p hg
    simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31822 p hg
    simpa only [d5849, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31824 (p : Pattern) (guard : d5849 p = 1) : d3745 p ≤ (0 : Int) + d2352 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3745, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31823 p hg
    simpa only [d3745, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3745, d2352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d3745, d2352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31825 (p : Pattern) (guard : d5849 p = 1) : d3746 p ≤ (0 : Int) + d2353 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31824 p hg
    simpa only [d3746, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31758 p hg
    simpa only [d3746, d2353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31826 (p : Pattern) (guard : d5847 p = 1) : d115 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14669 p hg
    simpa only [d5847, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31827 (p : Pattern) (guard : d5848 p = 1) : d115 p ≤ (0 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31826 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31828 (p : Pattern) (guard : d5849 p = 1) : d115 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31827 p hg
    simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5849, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31829 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31830 (p : Pattern) (guard : d5847 p = 1) : d3769 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3769, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3769, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3769, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31829 p hg
    simpa only [d5847, d3769, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31831 (p : Pattern) (guard : d5848 p = 1) : d3794 p ≤ (0 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31830 p hg
    simpa only [d5848, d3794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31832 (p : Pattern) (guard : d5849 p = 1) : d3795 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3795, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31831 p hg
    simpa only [d5849, d3795, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3795, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29551 p hg
    simpa only [d5849, d3795, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31833 (p : Pattern) (guard : d5849 p = 1) : d3796 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31828 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31832 p hg
    simpa only [d3796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31834 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31835 (p : Pattern) (guard : d5847 p = 1) : d3797 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3797, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d3797, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3797, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31834 p hg
    simpa only [d5847, d3797, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31836 (p : Pattern) (guard : d5848 p = 1) : d3798 p ≤ (0 : Int) + d116 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31835 p hg
    simpa only [d5848, d3798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31837 (p : Pattern) (guard : d5849 p = 1) : d3799 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3799, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31836 p hg
    simpa only [d5849, d3799, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3799, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29556 p hg
    simpa only [d5849, d3799, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31838 (p : Pattern) (guard : d5849 p = 1) : d3800 p ≤ (0 : Int) + d2337 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3800, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31837 p hg
    simpa only [d3800, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3800, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3800, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31839 (p : Pattern) (guard : d5849 p = 1) : d3801 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3801, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31833 p hg
    simpa only [d3801, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3801, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31838 p hg
    simpa only [d3801, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31840 (p : Pattern) (guard : d5849 p = 1) : d3802 p ≤ (0 : Int) + d2355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3802, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31825 p hg
    simpa only [d3802, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3802, d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31839 p hg
    simpa only [d3802, d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31841 (p : Pattern) (guard : d5849 p = 1) : d3803 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3803, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31782 p hg
    simpa only [d3803, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3803, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3803, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31842 (p : Pattern) (guard : d5849 p = 1) : d3804 p ≤ (0 : Int) + d2357 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3804, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31840 p hg
    simpa only [d3804, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3804, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31841 p hg
    simpa only [d3804, d2357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31843 (p : Pattern) (guard : d5849 p = 1) : d3805 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3805, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31782 p hg
    simpa only [d3805, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3805, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d3805, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31844 (p : Pattern) (guard : d5849 p = 1) : d3806 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3806, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31843 p hg
    simpa only [d3806, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3806, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3806, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31845 (p : Pattern) (guard : d5849 p = 1) : d3807 p ≤ (0 : Int) + d2360 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3807, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31842 p hg
    simpa only [d3807, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3807, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31844 p hg
    simpa only [d3807, d2360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31846 (p : Pattern) (guard : d5849 p = 1) : d3808 p ≤ (0 : Int) + d2336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31828 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31798 p hg
    simpa only [d3808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31847 (p : Pattern) (guard : d5849 p = 1) : d3809 p ≤ (0 : Int) + d2361 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3809, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31846 p hg
    simpa only [d3809, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3809, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3809, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31848 (p : Pattern) (guard : d5849 p = 1) : d3810 p ≤ (0 : Int) + d2362 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3810, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31806 p hg
    simpa only [d3810, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3810, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31847 p hg
    simpa only [d3810, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31849 (p : Pattern) (guard : d5849 p = 1) : d3811 p ≤ (0 : Int) + d2363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3811, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d3811, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3811, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31638 p hg
    simpa only [d3811, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31850 (p : Pattern) (guard : d5849 p = 1) : d3812 p ≤ (0 : Int) + d2364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3812, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31848 p hg
    simpa only [d3812, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3812, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31849 p hg
    simpa only [d3812, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31851 (p : Pattern) (guard : d5849 p = 1) : d3813 p ≤ (0 : Int) + d2365 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3813, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d3813, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3813, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31640 p hg
    simpa only [d3813, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31852 (p : Pattern) (guard : d5849 p = 1) : d3814 p ≤ (0 : Int) + d2366 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3814, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31851 p hg
    simpa only [d3814, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3814, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3814, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31853 (p : Pattern) (guard : d5849 p = 1) : d3815 p ≤ (0 : Int) + d2367 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3815, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31850 p hg
    simpa only [d3815, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3815, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31852 p hg
    simpa only [d3815, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31854 (p : Pattern) (guard : d5849 p = 1) : d3816 p ≤ (0 : Int) + d2368 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3816, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31845 p hg
    simpa only [d3816, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3816, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31853 p hg
    simpa only [d3816, d2368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31855 (p : Pattern) (guard : d5849 p = 1) : d3817 p ≤ (0 : Int) + d2369 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3817, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31821 p hg
    simpa only [d3817, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3817, d2369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31854 p hg
    simpa only [d3817, d2369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31856 (p : Pattern) (guard : d0 p = 1) : d3818 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31857 (p : Pattern) (guard : d5849 p = 1) : d3819 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3819, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31790 p hg
    simpa only [d5849, d3819, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3819, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31856 p hg
    simpa only [d5849, d3819, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31858 (p : Pattern) (guard : d5849 p = 1) : d3820 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31766 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31857 p hg
    simpa only [d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31859 (p : Pattern) (guard : d5849 p = 1) : d3821 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3821, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d3821, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3821, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3821, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31860 (p : Pattern) (guard : d5849 p = 1) : d3822 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3822, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31858 p hg
    simpa only [d3822, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3822, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31859 p hg
    simpa only [d3822, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31861 (p : Pattern) (guard : d0 p = 1) : d3824 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31862 (p : Pattern) (guard : d5849 p = 1) : d3825 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3825, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31790 p hg
    simpa only [d5849, d3825, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3825, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31861 p hg
    simpa only [d5849, d3825, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31863 (p : Pattern) (guard : d5849 p = 1) : d3826 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3826, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31862 p hg
    simpa only [d3826, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3826, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3826, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31864 (p : Pattern) (guard : d5849 p = 1) : d3827 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3827, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d3827, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3827, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31863 p hg
    simpa only [d3827, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31865 (p : Pattern) (guard : d5849 p = 1) : d3828 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31860 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31866 (p : Pattern) (guard : d5849 p = 1) : d3829 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3829, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31792 p hg
    simpa only [d3829, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3829, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3829, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31867 (p : Pattern) (guard : d5849 p = 1) : d3830 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3830, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d3830, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3830, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31866 p hg
    simpa only [d3830, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31868 (p : Pattern) (guard : d5849 p = 1) : d3831 p ≤ (0 : Int) + d2329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3831, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31813 p hg
    simpa only [d3831, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3831, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3831, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31869 (p : Pattern) (guard : d5849 p = 1) : d3832 p ≤ (0 : Int) + d2330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3832, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31814 p hg
    simpa only [d3832, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3832, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31868 p hg
    simpa only [d3832, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31870 (p : Pattern) (guard : d5849 p = 1) : d3833 p ≤ (0 : Int) + d2331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3833, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31867 p hg
    simpa only [d3833, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3833, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3833, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31871 (p : Pattern) (guard : d5849 p = 1) : d3834 p ≤ (0 : Int) + d2370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3834, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31865 p hg
    simpa only [d3834, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3834, d2370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31870 p hg
    simpa only [d3834, d2370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31872 (p : Pattern) (guard : d5849 p = 1) : d3835 p ≤ (0 : Int) + d2334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3835, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31870 p hg
    simpa only [d3835, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3835, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31785 p hg
    simpa only [d3835, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31873 (p : Pattern) (guard : d5849 p = 1) : d3836 p ≤ (0 : Int) + d2371 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3836, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31871 p hg
    simpa only [d3836, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3836, d2371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31872 p hg
    simpa only [d3836, d2371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31874 (p : Pattern) (guard : d5849 p = 1) : d3837 p ≤ (0 : Int) + d2354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3837, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31846 p hg
    simpa only [d3837, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3837, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31799 p hg
    simpa only [d3837, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31875 (p : Pattern) (guard : d5847 p = 1) : d119 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14677 p hg
    simpa only [d5847, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31876 (p : Pattern) (guard : d5848 p = 1) : d119 p ≤ (0 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31875 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31877 (p : Pattern) (guard : d5849 p = 1) : d119 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31876 p hg
    simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5849, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31878 (p : Pattern) (guard : d5849 p = 1) : d3838 p ≤ (0 : Int) + d2339 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31877 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31804 p hg
    simpa only [d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31879 (p : Pattern) (guard : d5849 p = 1) : d3839 p ≤ (0 : Int) + d2372 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3839, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31878 p hg
    simpa only [d3839, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3839, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31805 p hg
    simpa only [d3839, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31880 (p : Pattern) (guard : d5849 p = 1) : d3840 p ≤ (0 : Int) + d2373 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3840, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d3840, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3840, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31879 p hg
    simpa only [d3840, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31881 (p : Pattern) (guard : d5849 p = 1) : d3841 p ≤ (0 : Int) + d2374 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3841, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31880 p hg
    simpa only [d3841, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3841, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3841, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31882 (p : Pattern) (guard : d5849 p = 1) : d3842 p ≤ (0 : Int) + d2375 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3842, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31881 p hg
    simpa only [d3842, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3842, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3842, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31883 (p : Pattern) (guard : d5849 p = 1) : d3843 p ≤ (0 : Int) + d2376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3843, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31873 p hg
    simpa only [d3843, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3843, d2376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31882 p hg
    simpa only [d3843, d2376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31884 (p : Pattern) (guard : d5849 p = 1) : d3844 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3844, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d3844, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3844, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d3844, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31885 (p : Pattern) (guard : d5849 p = 1) : d3845 p ≤ (0 : Int) + d2356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3845, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3845, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3845, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3845, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31886 (p : Pattern) (guard : d5849 p = 1) : d3846 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3846, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31884 p hg
    simpa only [d3846, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3846, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31885 p hg
    simpa only [d3846, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31887 (p : Pattern) (guard : d5849 p = 1) : d3847 p ≤ (0 : Int) + d2358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3847, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d3847, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3847, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d3847, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31888 (p : Pattern) (guard : d5849 p = 1) : d3848 p ≤ (0 : Int) + d2359 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3848, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31887 p hg
    simpa only [d3848, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3848, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3848, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31889 (p : Pattern) (guard : d5849 p = 1) : d3849 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3849, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31886 p hg
    simpa only [d3849, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3849, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31888 p hg
    simpa only [d3849, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31890 (p : Pattern) (guard : d5849 p = 1) : d3850 p ≤ (0 : Int) + d2380 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3850, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31879 p hg
    simpa only [d3850, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3850, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3850, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31891 (p : Pattern) (guard : d5849 p = 1) : d3851 p ≤ (0 : Int) + d2381 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3851, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31890 p hg
    simpa only [d3851, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3851, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3851, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31892 (p : Pattern) (guard : d5849 p = 1) : d3852 p ≤ (0 : Int) + d2382 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3852, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31891 p hg
    simpa only [d3852, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3852, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3852, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31893 (p : Pattern) (guard : d5849 p = 1) : d3853 p ≤ (0 : Int) + d2383 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3853, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31889 p hg
    simpa only [d3853, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3853, d2383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31892 p hg
    simpa only [d3853, d2383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31894 (p : Pattern) (guard : d5849 p = 1) : d3854 p ≤ (0 : Int) + d2384 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3854, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31883 p hg
    simpa only [d3854, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3854, d2384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31893 p hg
    simpa only [d3854, d2384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31895 (p : Pattern) (guard : d5849 p = 1) : d3855 p ≤ (0 : Int) + d2385 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3855, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31855 p hg
    simpa only [d3855, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3855, d2385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31894 p hg
    simpa only [d3855, d2385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31896 (p : Pattern) (guard : d5849 p = 1) : d3856 p ≤ (0 : Int) + d2386 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3856, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31785 p hg
    simpa only [d3856, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3856, d2386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3856, d2386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31897 (p : Pattern) (guard : d5849 p = 1) : d3857 p ≤ (0 : Int) + d2387 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3857, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31896 p hg
    simpa only [d3857, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3857, d2387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3857, d2387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31898 (p : Pattern) (guard : d5849 p = 1) : d3858 p ≤ (0 : Int) + d2388 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3858, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31897 p hg
    simpa only [d3858, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3858, d2388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3858, d2388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31899 (p : Pattern) (guard : d5849 p = 1) : d3859 p ≤ (0 : Int) + d2389 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3859, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31898 p hg
    simpa only [d3859, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3859, d2389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3859, d2389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31900 (p : Pattern) (guard : d5849 p = 1) : d3860 p ≤ (0 : Int) + d2390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3860, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31894 p hg
    simpa only [d3860, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3860, d2390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31899 p hg
    simpa only [d3860, d2390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31901 (p : Pattern) (guard : d5849 p = 1) : d3861 p ≤ (0 : Int) + d2391 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3861, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31895 p hg
    simpa only [d3861, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3861, d2391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31900 p hg
    simpa only [d3861, d2391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31902 (p : Pattern) (guard : d5849 p = 1) : d3746 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31764 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31768 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31903 (p : Pattern) (guard : d5849 p = 1) : d3862 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3862, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31902 p hg
    simpa only [d3862, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3862, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31783 p hg
    simpa only [d3862, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31904 (p : Pattern) (guard : d5849 p = 1) : d3863 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3863, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31903 p hg
    simpa only [d3863, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3863, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31786 p hg
    simpa only [d3863, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31905 (p : Pattern) (guard : d5849 p = 1) : d3864 p ≤ (0 : Int) + d2395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3864, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31904 p hg
    simpa only [d3864, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3864, d2395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31820 p hg
    simpa only [d3864, d2395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31906 (p : Pattern) (guard : d5849 p = 1) : d3802 p ≤ (0 : Int) + d2377 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3802, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31768 p hg
    simpa only [d3802, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3802, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31839 p hg
    simpa only [d3802, d2377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31907 (p : Pattern) (guard : d5849 p = 1) : d3804 p ≤ (0 : Int) + d2378 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3804, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31906 p hg
    simpa only [d3804, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3804, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31841 p hg
    simpa only [d3804, d2378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31908 (p : Pattern) (guard : d5849 p = 1) : d3807 p ≤ (0 : Int) + d2379 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3807, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31907 p hg
    simpa only [d3807, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3807, d2379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31844 p hg
    simpa only [d3807, d2379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31909 (p : Pattern) (guard : d5849 p = 1) : d3816 p ≤ (0 : Int) + d2396 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3816, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31908 p hg
    simpa only [d3816, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3816, d2396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31853 p hg
    simpa only [d3816, d2396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31910 (p : Pattern) (guard : d5849 p = 1) : d3865 p ≤ (0 : Int) + d2397 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3865, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31905 p hg
    simpa only [d3865, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3865, d2397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31909 p hg
    simpa only [d3865, d2397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31911 (p : Pattern) (guard : d5849 p = 1) : d3866 p ≤ (0 : Int) + d2398 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3866, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31910 p hg
    simpa only [d3866, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3866, d2398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31894 p hg
    simpa only [d3866, d2398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31912 (p : Pattern) (guard : d5849 p = 1) : d3867 p ≤ (0 : Int) + d2399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3867, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31894 p hg
    simpa only [d3867, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3867, d2399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3867, d2399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31913 (p : Pattern) (guard : d5849 p = 1) : d3868 p ≤ (0 : Int) + d2400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3868, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31911 p hg
    simpa only [d3868, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3868, d2400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31912 p hg
    simpa only [d3868, d2400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31914 (p : Pattern) (guard : d5849 p = 1) : d3869 p ≤ (0 : Int) + d2401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3869, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31901 p hg
    simpa only [d3869, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3869, d2401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31913 p hg
    simpa only [d3869, d2401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31915 (p : Pattern) (guard : d5849 p = 1) : d3870 p ≤ (0 : Int) + d2402 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3870, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31718 p hg
    simpa only [d3870, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3870, d2402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31914 p hg
    simpa only [d3870, d2402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31916 (p : Pattern) (guard : d5849 p = 1) : d3871 p ≤ (0 : Int) + d2403 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3871, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31744 p hg
    simpa only [d3871, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3871, d2403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31915 p hg
    simpa only [d3871, d2403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31917 (p : Pattern) (guard : d5849 p = 1) : d3660 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31690 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31650 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31918 (p : Pattern) (guard : d0 p = 1) : d3872 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31919 (p : Pattern) (guard : d5849 p = 1) : d3873 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3873, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31579 p hg
    simpa only [d5849, d3873, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3873, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31918 p hg
    simpa only [d5849, d3873, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
