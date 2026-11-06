/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons198
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27860 (p : Pattern) (guard : d5847 p = 1) : d3535 p ≤ (0 : Int) + d4032 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3535, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27848 p hg
    simpa only [d3535, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3535, d4032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27859 p hg
    simpa only [d3535, d4032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27861 (p : Pattern) (guard : d5847 p = 1) : d3536 p ≤ (0 : Int) + d4033 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3536, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27789 p hg
    simpa only [d3536, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3536, d4033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27860 p hg
    simpa only [d3536, d4033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27862 (p : Pattern) (guard : d5847 p = 1) : d3537 p ≤ (0 : Int) + d4034 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3537, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27516 p hg
    simpa only [d3537, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3537, d4034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27861 p hg
    simpa only [d3537, d4034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27863 (p : Pattern) (guard : d5847 p = 1) : d3538 p ≤ (0 : Int) + d4035 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3538, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27770 p hg
    simpa only [d3538, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3538, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27862 p hg
    simpa only [d3538, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27864 (p : Pattern) (guard : d5847 p = 1) : d3539 p ≤ (0 : Int) + d4036 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3539, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27696 p hg
    simpa only [d3539, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3539, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27863 p hg
    simpa only [d3539, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27865 (p : Pattern) (guard : d5842 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare27866 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27867 (p : Pattern) (guard : d6558 p = 1) : d3225 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27866 p hg
    simpa only [d6558, d3225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27868 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26332 p hg
    simpa only [d6558, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27869 (p : Pattern) (guard : d6558 p = 1) : d3227 p ≤ (0 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27867 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27870 (p : Pattern) (guard : d6558 p = 1) : d3228 p ≤ (0 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27869 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27871 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6559 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, d6559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d6558, d3226, d6559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27872 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6560 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d6560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27873 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27872 p hg
    simpa only [d6561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d6561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27874 (p : Pattern) (guard : d6558 p = 1) : d3229 p ≤ (0 : Int) + d6562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3229, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27870 p hg
    simpa only [d3229, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3229, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d3229, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27875 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6563 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, d6563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, d6563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, d6563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26354 p hg
    simpa only [d6558, d3226, d6563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27876 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6564 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27875 p hg
    simpa only [d6564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27877 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6565 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27876 p hg
    simpa only [d6565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27875 p hg
    simpa only [d6565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27878 (p : Pattern) (guard : d6558 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare27879 (p : Pattern) (guard : d6558 p = 1) : d3230 p ≤ (0 : Int) + d6566 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27877 p hg
    simpa only [d3230, d6566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3230, d6566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3230, d6566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27880 (p : Pattern) (guard : d6558 p = 1) : d3231 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3231, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27874 p hg
    simpa only [d3231, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3231, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d3231, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27881 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27882 (p : Pattern) (guard : d6558 p = 1) : d3232 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27881 p hg
    simpa only [d6558, d3232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27883 (p : Pattern) (guard : d6558 p = 1) : d3233 p ≤ (0 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27882 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27884 (p : Pattern) (guard : d6558 p = 1) : d3234 p ≤ (0 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27883 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27885 (p : Pattern) (guard : d6558 p = 1) : d3235 p ≤ (0 : Int) + d6562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3235, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27884 p hg
    simpa only [d3235, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3235, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d3235, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27886 (p : Pattern) (guard : d6558 p = 1) : d3236 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3236, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27885 p hg
    simpa only [d3236, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3236, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d3236, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27887 (p : Pattern) (guard : d6558 p = 1) : d3237 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27880 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27886 p hg
    simpa only [d3237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27888 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27889 (p : Pattern) (guard : d6558 p = 1) : d3238 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27888 p hg
    simpa only [d3238, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3238, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d3238, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27890 (p : Pattern) (guard : d5842 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare27891 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27890 p hg
    simpa only [d6558, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d6558, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27892 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6568 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3239, d6568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27890 p hg
    simpa only [d6558, d3239, d6568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3239, d6568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d6558, d3239, d6568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27893 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6569 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d6569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27894 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6570 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27893 p hg
    simpa only [d6570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d6570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27895 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6571 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27894 p hg
    simpa only [d6571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27896 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6572 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3239, d6572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27890 p hg
    simpa only [d6558, d3239, d6572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3239, d6572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d6558, d3239, d6572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27897 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6573 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27896 p hg
    simpa only [d6573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27898 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6574 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27897 p hg
    simpa only [d6574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27896 p hg
    simpa only [d6574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27899 (p : Pattern) (guard : d6558 p = 1) : d3240 p ≤ (0 : Int) + d6575 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27898 p hg
    simpa only [d3240, d6575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3240, d6575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3240, d6575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27900 (p : Pattern) (guard : d6558 p = 1) : d3241 p ≤ (0 : Int) + d6576 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27895 p hg
    simpa only [d3241, d6576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3241, d6576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27899 p hg
    simpa only [d3241, d6576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27901 (p : Pattern) (guard : d6558 p = 1) : d3242 p ≤ (0 : Int) + d6577 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d3242, d6577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3242, d6577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27900 p hg
    simpa only [d3242, d6577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27902 (p : Pattern) (guard : d6558 p = 1) : d3243 p ≤ (0 : Int) + d6578 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3243, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27887 p hg
    simpa only [d3243, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3243, d6578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d3243, d6578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27903 (p : Pattern) (guard : d5842 p = 1) : d9 p ≤ (0 : Int) + d9 p := by
  omega
theorem compare27904 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27903 p hg
    simpa only [d6558, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d6558, d3244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27905 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d3244 p := by
  omega
theorem compare27906 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6579 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27904 p hg
    simpa only [d6579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27905 p hg
    simpa only [d6579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27907 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6580 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27906 p hg
    simpa only [d6580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27905 p hg
    simpa only [d6580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27908 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6581 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27904 p hg
    simpa only [d6581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27907 p hg
    simpa only [d6581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27909 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6582 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3244, d6582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27903 p hg
    simpa only [d6558, d3244, d6582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3244, d6582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3244, d6582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27910 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6583 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27904 p hg
    simpa only [d6583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27909 p hg
    simpa only [d6583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27911 (p : Pattern) (guard : d6558 p = 1) : d3244 p ≤ (0 : Int) + d6584 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27910 p hg
    simpa only [d6584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27909 p hg
    simpa only [d6584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27912 (p : Pattern) (guard : d6558 p = 1) : d3245 p ≤ (0 : Int) + d6585 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3245, d6585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27911 p hg
    simpa only [d3245, d6585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3245, d6585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3245, d6585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27913 (p : Pattern) (guard : d6558 p = 1) : d3246 p ≤ (0 : Int) + d6586 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3246, d6586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27908 p hg
    simpa only [d3246, d6586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3246, d6586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27912 p hg
    simpa only [d3246, d6586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27914 (p : Pattern) (guard : d6558 p = 1) : d3247 p ≤ (0 : Int) + d6587 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3247, d6587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27913 p hg
    simpa only [d3247, d6587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3247, d6587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3247, d6587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27915 (p : Pattern) (guard : d6558 p = 1) : d3248 p ≤ (0 : Int) + d6588 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d3248, d6588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3248, d6588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27914 p hg
    simpa only [d3248, d6588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27916 (p : Pattern) (guard : d6558 p = 1) : d3249 p ≤ (0 : Int) + d6589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3249, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27902 p hg
    simpa only [d3249, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3249, d6589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27915 p hg
    simpa only [d3249, d6589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27917 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6590 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, d6590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, d6590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, d6590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d6558, d3226, d6590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27918 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6591 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27917 p hg
    simpa only [d6591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27919 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6592 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3226, d6592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3226, d6592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3226, d6592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d6558, d3226, d6592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27920 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6593 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27919 p hg
    simpa only [d6593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27921 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6594 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27918 p hg
    simpa only [d6594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27920 p hg
    simpa only [d6594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27922 (p : Pattern) (guard : d6558 p = 1) : d3226 p ≤ (0 : Int) + d6595 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d6595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27921 p hg
    simpa only [d6595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27923 (p : Pattern) (guard : d5842 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare27924 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26354 p hg
    simpa only [d6558, d3250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27925 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6596 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, d6596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, d6596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, d6596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d6558, d3250, d6596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27926 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6597 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27925 p hg
    simpa only [d6597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27927 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6598 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, d6598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, d6598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, d6598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d6558, d3250, d6598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27928 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6599 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, d6599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, d6599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, d6599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3250, d6599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27929 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6600 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d6600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27928 p hg
    simpa only [d6600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27930 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6601 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27926 p hg
    simpa only [d6601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27929 p hg
    simpa only [d6601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27931 (p : Pattern) (guard : d6558 p = 1) : d3251 p ≤ (0 : Int) + d6602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27930 p hg
    simpa only [d3251, d6602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3251, d6602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27932 (p : Pattern) (guard : d6558 p = 1) : d3252 p ≤ (0 : Int) + d6603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3252, d6603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3252, d6603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3252, d6603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27931 p hg
    simpa only [d3252, d6603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27933 (p : Pattern) (guard : d5842 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare27934 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27933 p hg
    simpa only [d6558, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d6558, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27935 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d3253 p := by
  omega
theorem compare27936 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6604 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27934 p hg
    simpa only [d6604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27935 p hg
    simpa only [d6604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27937 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6605 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3253, d6605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27933 p hg
    simpa only [d6558, d3253, d6605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3253, d6605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d6558, d3253, d6605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27938 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6606 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27937 p hg
    simpa only [d6606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27935 p hg
    simpa only [d6606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27939 (p : Pattern) (guard : d6558 p = 1) : d3253 p ≤ (0 : Int) + d6607 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27936 p hg
    simpa only [d6607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27938 p hg
    simpa only [d6607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27940 (p : Pattern) (guard : d6558 p = 1) : d3254 p ≤ (0 : Int) + d6608 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3254, d6608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27939 p hg
    simpa only [d3254, d6608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3254, d6608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3254, d6608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27941 (p : Pattern) (guard : d6558 p = 1) : d3255 p ≤ (0 : Int) + d6609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3255, d6609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3255, d6609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3255, d6609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27940 p hg
    simpa only [d3255, d6609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27942 (p : Pattern) (guard : d6558 p = 1) : d3256 p ≤ (0 : Int) + d6610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3256, d6610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27932 p hg
    simpa only [d3256, d6610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3256, d6610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27941 p hg
    simpa only [d3256, d6610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27943 (p : Pattern) (guard : d5842 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare27944 (p : Pattern) (guard : d6558 p = 1) : d3257 p ≤ (0 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27943 p hg
    simpa only [d6558, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d6558, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27945 (p : Pattern) (guard : d6558 p = 1) : d3257 p ≤ (0 : Int) + d3257 p := by
  omega
theorem compare27946 (p : Pattern) (guard : d6558 p = 1) : d3257 p ≤ (0 : Int) + d6611 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27944 p hg
    simpa only [d6611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27945 p hg
    simpa only [d6611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27947 (p : Pattern) (guard : d6558 p = 1) : d3257 p ≤ (0 : Int) + d6612 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27946 p hg
    simpa only [d6612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27945 p hg
    simpa only [d6612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27948 (p : Pattern) (guard : d6558 p = 1) : d3258 p ≤ (0 : Int) + d6613 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3258, d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27947 p hg
    simpa only [d3258, d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3258, d6613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3258, d6613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27949 (p : Pattern) (guard : d6558 p = 1) : d3259 p ≤ (0 : Int) + d6614 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3259, d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3259, d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3259, d6614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27948 p hg
    simpa only [d3259, d6614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27950 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6615 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3239, d6615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27890 p hg
    simpa only [d6558, d3239, d6615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3239, d6615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d6558, d3239, d6615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27951 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27950 p hg
    simpa only [d6616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27952 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d3239 p := by
  omega
theorem compare27953 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d6617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27952 p hg
    simpa only [d6617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27954 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6618 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27951 p hg
    simpa only [d6618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27953 p hg
    simpa only [d6618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27955 (p : Pattern) (guard : d6558 p = 1) : d3239 p ≤ (0 : Int) + d6619 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d6619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27954 p hg
    simpa only [d6619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27956 (p : Pattern) (guard : d6558 p = 1) : d3260 p ≤ (0 : Int) + d6620 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3260, d6620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27955 p hg
    simpa only [d3260, d6620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3260, d6620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3260, d6620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27957 (p : Pattern) (guard : d6558 p = 1) : d3261 p ≤ (0 : Int) + d6621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3261, d6621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27949 p hg
    simpa only [d3261, d6621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3261, d6621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d3261, d6621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27958 (p : Pattern) (guard : d6558 p = 1) : d3262 p ≤ (0 : Int) + d6622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3262, d6622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27942 p hg
    simpa only [d3262, d6622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3262, d6622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27957 p hg
    simpa only [d3262, d6622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27959 (p : Pattern) (guard : d6558 p = 1) : d3263 p ≤ (0 : Int) + d6623 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3263, d6623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d3263, d6623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3263, d6623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3263, d6623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27960 (p : Pattern) (guard : d6558 p = 1) : d3264 p ≤ (0 : Int) + d6624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3264, d6624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27959 p hg
    simpa only [d3264, d6624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3264, d6624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d3264, d6624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27961 (p : Pattern) (guard : d6558 p = 1) : d3265 p ≤ (0 : Int) + d6625 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3265, d6625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27908 p hg
    simpa only [d3265, d6625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3265, d6625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3265, d6625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27962 (p : Pattern) (guard : d6558 p = 1) : d3266 p ≤ (0 : Int) + d6626 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3266, d6626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27961 p hg
    simpa only [d3266, d6626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3266, d6626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3266, d6626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27963 (p : Pattern) (guard : d6558 p = 1) : d3267 p ≤ (0 : Int) + d6627 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3267, d6627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27960 p hg
    simpa only [d3267, d6627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3267, d6627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27962 p hg
    simpa only [d3267, d6627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27964 (p : Pattern) (guard : d6558 p = 1) : d3268 p ≤ (0 : Int) + d6628 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3268, d6628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27958 p hg
    simpa only [d3268, d6628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3268, d6628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27963 p hg
    simpa only [d3268, d6628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27965 (p : Pattern) (guard : d6558 p = 1) : d3269 p ≤ (0 : Int) + d6629 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3269, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27916 p hg
    simpa only [d3269, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3269, d6629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27964 p hg
    simpa only [d3269, d6629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27966 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27967 (p : Pattern) (guard : d6558 p = 1) : d3270 p ≤ (0 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d6558, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27966 p hg
    simpa only [d6558, d3270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27968 (p : Pattern) (guard : d6558 p = 1) : d3271 p ≤ (0 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27967 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27969 (p : Pattern) (guard : d6558 p = 1) : d3272 p ≤ (0 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27968 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d3272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27970 (p : Pattern) (guard : d6558 p = 1) : d3273 p ≤ (0 : Int) + d6562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3273, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27969 p hg
    simpa only [d3273, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3273, d6562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d3273, d6562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27971 (p : Pattern) (guard : d6558 p = 1) : d3274 p ≤ (0 : Int) + d6567 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3274, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27970 p hg
    simpa only [d3274, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3274, d6567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d3274, d6567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27972 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d6630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27973 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6631 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27972 p hg
    simpa only [d6631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d6631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27974 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6632 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27973 p hg
    simpa only [d6632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27975 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6633 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3250, d6633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d6558, d3250, d6633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3250, d6633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d6558, d3250, d6633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27976 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d6634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27977 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6635 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27976 p hg
    simpa only [d6635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d6635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27978 (p : Pattern) (guard : d6558 p = 1) : d3251 p ≤ (0 : Int) + d6636 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27977 p hg
    simpa only [d3251, d6636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3251, d6636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3251, d6636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27979 (p : Pattern) (guard : d6558 p = 1) : d3275 p ≤ (0 : Int) + d6637 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27974 p hg
    simpa only [d3275, d6637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3275, d6637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27978 p hg
    simpa only [d3275, d6637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27980 (p : Pattern) (guard : d6558 p = 1) : d3276 p ≤ (0 : Int) + d6638 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3276, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27971 p hg
    simpa only [d3276, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3276, d6638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27979 p hg
    simpa only [d3276, d6638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27981 (p : Pattern) (guard : d6558 p = 1) : d3277 p ≤ (0 : Int) + d6639 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27900 p hg
    simpa only [d3277, d6639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3277, d6639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27913 p hg
    simpa only [d3277, d6639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27982 (p : Pattern) (guard : d6558 p = 1) : d3278 p ≤ (0 : Int) + d6640 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3278, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27980 p hg
    simpa only [d3278, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3278, d6640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27981 p hg
    simpa only [d3278, d6640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27983 (p : Pattern) (guard : d5842 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  omega
theorem compare27984 (p : Pattern) (guard : d6558 p = 1) : d3279 p ≤ (0 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27983 p hg
    simpa only [d6558, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d6558, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27985 (p : Pattern) (guard : d6558 p = 1) : d3279 p ≤ (0 : Int) + d3279 p := by
  omega
theorem compare27986 (p : Pattern) (guard : d6558 p = 1) : d3279 p ≤ (0 : Int) + d6641 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27984 p hg
    simpa only [d6641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27985 p hg
    simpa only [d6641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27987 (p : Pattern) (guard : d6558 p = 1) : d3279 p ≤ (0 : Int) + d6642 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27986 p hg
    simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27985 p hg
    simpa only [d6642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27988 (p : Pattern) (guard : d6558 p = 1) : d3279 p ≤ (0 : Int) + d6643 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27984 p hg
    simpa only [d6643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27987 p hg
    simpa only [d6643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27989 (p : Pattern) (guard : d6558 p = 1) : d3280 p ≤ (0 : Int) + d6644 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3280, d6644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27987 p hg
    simpa only [d3280, d6644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3280, d6644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3280, d6644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27990 (p : Pattern) (guard : d6558 p = 1) : d3281 p ≤ (0 : Int) + d6645 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3281, d6645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27988 p hg
    simpa only [d3281, d6645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3281, d6645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27989 p hg
    simpa only [d3281, d6645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27991 (p : Pattern) (guard : d6558 p = 1) : d3282 p ≤ (0 : Int) + d6646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27900 p hg
    simpa only [d3282, d6646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3282, d6646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d3282, d6646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27992 (p : Pattern) (guard : d6558 p = 1) : d3257 p ≤ (0 : Int) + d6647 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27944 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27947 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27993 (p : Pattern) (guard : d6558 p = 1) : d3283 p ≤ (0 : Int) + d6648 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3283, d6648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27992 p hg
    simpa only [d3283, d6648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3283, d6648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27948 p hg
    simpa only [d3283, d6648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27994 (p : Pattern) (guard : d6558 p = 1) : d3284 p ≤ (0 : Int) + d6649 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3284, d6649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d3284, d6649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3284, d6649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3284, d6649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27995 (p : Pattern) (guard : d6558 p = 1) : d3285 p ≤ (0 : Int) + d6650 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27991 p hg
    simpa only [d3285, d6650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3285, d6650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d3285, d6650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27996 (p : Pattern) (guard : d6558 p = 1) : d3286 p ≤ (0 : Int) + d6651 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3286, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27982 p hg
    simpa only [d3286, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3286, d6651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27995 p hg
    simpa only [d3286, d6651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27997 (p : Pattern) (guard : d6558 p = 1) : d3250 p ≤ (0 : Int) + d6652 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27930 p hg
    simpa only [d6652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27998 (p : Pattern) (guard : d6558 p = 1) : d3287 p ≤ (0 : Int) + d6653 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3287, d6653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d3287, d6653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3287, d6653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d3287, d6653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27999 (p : Pattern) (guard : d6558 p = 1) : d3288 p ≤ (0 : Int) + d6654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d3288, d6654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27941 p hg
    simpa only [d3288, d6654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d3288, d6654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27998 p hg
    simpa only [d3288, d6654, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
