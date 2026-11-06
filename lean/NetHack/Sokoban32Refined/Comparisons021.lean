/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2940 (p : Pattern) (guard : d1174 p = 1) : d310 p ≤ (0 : Int) + d677 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d310, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d310, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d310, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2939 p hg
    simpa only [d310, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2941 (p : Pattern) (guard : d1174 p = 1) : d311 p ≤ (0 : Int) + d678 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d311, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d311, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d311, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2940 p hg
    simpa only [d311, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2942 (p : Pattern) (guard : d1174 p = 1) : d307 p ≤ (0 : Int) + d679 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d307, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d1174, d307, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d307, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1174, d307, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2943 (p : Pattern) (guard : d1174 p = 1) : d307 p ≤ (0 : Int) + d680 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2942 p hg
    simpa only [d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2944 (p : Pattern) (guard : d1174 p = 1) : d312 p ≤ (0 : Int) + d659 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1174, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2945 (p : Pattern) (guard : d1174 p = 1) : d312 p ≤ (0 : Int) + d681 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d312, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d1174, d312, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d312, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1174, d312, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2946 (p : Pattern) (guard : d1174 p = 1) : d312 p ≤ (0 : Int) + d682 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2945 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2947 (p : Pattern) (guard : d1174 p = 1) : d313 p ≤ (0 : Int) + d683 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d313, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2943 p hg
    simpa only [d313, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d313, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2946 p hg
    simpa only [d313, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2948 (p : Pattern) (guard : d1174 p = 1) : d314 p ≤ (0 : Int) + d684 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d314, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2941 p hg
    simpa only [d314, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d314, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2947 p hg
    simpa only [d314, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2949 (p : Pattern) (guard : d1174 p = 1) : d315 p ≤ (0 : Int) + d685 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d315, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2938 p hg
    simpa only [d315, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d315, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2948 p hg
    simpa only [d315, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2950 (p : Pattern) (guard : d1174 p = 1) : d316 p ≤ (0 : Int) + d686 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d316, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2929 p hg
    simpa only [d316, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d316, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2949 p hg
    simpa only [d316, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2951 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2952 (p : Pattern) (guard : d1174 p = 1) : d298 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2951 p hg
    simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2953 (p : Pattern) (guard : d1174 p = 1) : d299 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2952 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2954 (p : Pattern) (guard : d1174 p = 1) : d300 p ≤ (0 : Int) + d654 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2955 (p : Pattern) (guard : d1174 p = 1) : d301 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d301, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2954 p hg
    simpa only [d301, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d301, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2914 p hg
    simpa only [d301, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2956 (p : Pattern) (guard : d1174 p = 1) : d317 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d317, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1174, d317, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d317, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1174, d317, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2957 (p : Pattern) (guard : d1174 p = 1) : d318 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d318, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2952 p hg
    simpa only [d318, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d318, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2956 p hg
    simpa only [d318, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2958 (p : Pattern) (guard : d1174 p = 1) : d319 p ≤ (0 : Int) + d664 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2959 (p : Pattern) (guard : d1174 p = 1) : d320 p ≤ (0 : Int) + d687 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d320, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2958 p hg
    simpa only [d320, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d320, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d320, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2960 (p : Pattern) (guard : d1174 p = 1) : d321 p ≤ (0 : Int) + d688 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d321, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2955 p hg
    simpa only [d321, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d321, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2959 p hg
    simpa only [d321, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2961 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2962 (p : Pattern) (guard : d1174 p = 1) : d309 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2963 (p : Pattern) (guard : d1174 p = 1) : d310 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2962 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2964 (p : Pattern) (guard : d1174 p = 1) : d311 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d311, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2953 p hg
    simpa only [d311, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d311, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2963 p hg
    simpa only [d311, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2965 (p : Pattern) (guard : d1174 p = 1) : d313 p ≤ (0 : Int) + d689 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d313, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2937 p hg
    simpa only [d313, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d313, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2944 p hg
    simpa only [d313, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2966 (p : Pattern) (guard : d1174 p = 1) : d314 p ≤ (0 : Int) + d690 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d314, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2964 p hg
    simpa only [d314, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d314, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2965 p hg
    simpa only [d314, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2967 (p : Pattern) (guard : d1174 p = 1) : d322 p ≤ (0 : Int) + d691 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d322, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2957 p hg
    simpa only [d322, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d322, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2926 p hg
    simpa only [d322, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2968 (p : Pattern) (guard : d1174 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2969 (p : Pattern) (guard : d1174 p = 1) : d323 p ≤ (0 : Int) + d692 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d323, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2946 p hg
    simpa only [d323, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d323, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2968 p hg
    simpa only [d323, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2970 (p : Pattern) (guard : d1174 p = 1) : d324 p ≤ (0 : Int) + d693 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d324, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2967 p hg
    simpa only [d324, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d324, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2969 p hg
    simpa only [d324, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2971 (p : Pattern) (guard : d1174 p = 1) : d325 p ≤ (0 : Int) + d694 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d325, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2966 p hg
    simpa only [d325, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d325, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2970 p hg
    simpa only [d325, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2972 (p : Pattern) (guard : d1174 p = 1) : d326 p ≤ (0 : Int) + d695 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d326, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2960 p hg
    simpa only [d326, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d326, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2971 p hg
    simpa only [d326, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2973 (p : Pattern) (guard : d1174 p = 1) : d327 p ≤ (0 : Int) + d696 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d327, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2950 p hg
    simpa only [d327, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d327, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2972 p hg
    simpa only [d327, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2974 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2975 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d328 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2974 p hg
    simpa only [d984, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2976 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2977 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d293, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2976 p hg
    simpa only [d984, d293, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2978 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2977 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2979 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2980 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d332 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2979 p hg
    simpa only [d984, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2981 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2982 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d334 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d984, d294, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2981 p hg
    simpa only [d984, d294, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2983 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d335 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2982 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2984 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2985 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d336 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2984 p hg
    simpa only [d984, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2986 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d337 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2987 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d338 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d984, d295, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2986 p hg
    simpa only [d984, d295, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2988 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d339 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2985 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2987 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2989 (p : Pattern) (guard : d984 p = 1) : d296 p ≤ (0 : Int) + d340 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d296, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2983 p hg
    simpa only [d296, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d296, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2988 p hg
    simpa only [d296, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2990 (p : Pattern) (guard : d984 p = 1) : d297 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d297, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d297, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d297, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2989 p hg
    simpa only [d297, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2991 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d342 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2992 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d293, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d293, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d293, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2991 p hg
    simpa only [d984, d293, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2993 (p : Pattern) (guard : d984 p = 1) : d293 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2992 p hg
    simpa only [d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2994 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2995 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d298, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2994 p hg
    simpa only [d984, d298, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2996 (p : Pattern) (guard : d984 p = 1) : d299 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d299, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d299, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d299, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2995 p hg
    simpa only [d299, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2997 (p : Pattern) (guard : d984 p = 1) : d300 p ≤ (0 : Int) + d348 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2993 p hg
    simpa only [d300, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d300, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2998 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2999 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d349 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d294, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare854 p hg
    simpa only [d984, d294, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d294, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d984, d294, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3000 (p : Pattern) (guard : d984 p = 1) : d294 p ≤ (0 : Int) + d350 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2980 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2999 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3001 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d295, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d984, d295, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d295, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d984, d295, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3002 (p : Pattern) (guard : d984 p = 1) : d295 p ≤ (0 : Int) + d352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2985 p hg
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3001 p hg
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3003 (p : Pattern) (guard : d984 p = 1) : d296 p ≤ (0 : Int) + d353 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d296, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3000 p hg
    simpa only [d296, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d296, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d296, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3004 (p : Pattern) (guard : d984 p = 1) : d301 p ≤ (0 : Int) + d354 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d301, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2997 p hg
    simpa only [d301, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d301, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d301, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3005 (p : Pattern) (guard : d984 p = 1) : d302 p ≤ (0 : Int) + d355 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d302, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2990 p hg
    simpa only [d302, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d302, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3004 p hg
    simpa only [d302, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3006 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3007 (p : Pattern) (guard : d984 p = 1) : d303 p ≤ (0 : Int) + d356 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3006 p hg
    simpa only [d984, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3008 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3009 (p : Pattern) (guard : d984 p = 1) : d304 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d304, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d984, d304, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d304, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d984, d304, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3010 (p : Pattern) (guard : d984 p = 1) : d305 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d305, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3007 p hg
    simpa only [d305, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d305, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3009 p hg
    simpa only [d305, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3011 (p : Pattern) (guard : d984 p = 1) : d306 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d306, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d306, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d306, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3010 p hg
    simpa only [d306, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3012 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3013 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d361 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3012 p hg
    simpa only [d984, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3014 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d342 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3015 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d362 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d984, d307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3014 p hg
    simpa only [d984, d307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3016 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d363 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3015 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3017 (p : Pattern) (guard : d984 p = 1) : d308 p ≤ (0 : Int) + d364 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d308, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d308, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d308, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3016 p hg
    simpa only [d308, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3018 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3019 (p : Pattern) (guard : d984 p = 1) : d304 p ≤ (0 : Int) + d356 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3018 p hg
    simpa only [d984, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3020 (p : Pattern) (guard : d984 p = 1) : d309 p ≤ (0 : Int) + d365 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d309, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d984, d309, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d309, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d984, d309, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3021 (p : Pattern) (guard : d984 p = 1) : d310 p ≤ (0 : Int) + d366 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d310, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d310, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d310, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d310, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3022 (p : Pattern) (guard : d984 p = 1) : d311 p ≤ (0 : Int) + d367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d311, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d311, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d311, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d311, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3023 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d368 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d307, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d984, d307, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d307, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d307, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3024 (p : Pattern) (guard : d984 p = 1) : d307 p ≤ (0 : Int) + d369 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3013 p hg
    simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3023 p hg
    simpa only [d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3025 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3026 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d370 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3025 p hg
    simpa only [d984, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3027 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d984, d312, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d312, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3028 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d372 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3026 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3027 p hg
    simpa only [d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3029 (p : Pattern) (guard : d984 p = 1) : d313 p ≤ (0 : Int) + d373 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d313, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3024 p hg
    simpa only [d313, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d313, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3028 p hg
    simpa only [d313, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3030 (p : Pattern) (guard : d984 p = 1) : d314 p ≤ (0 : Int) + d374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d314, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3022 p hg
    simpa only [d314, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d314, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3029 p hg
    simpa only [d314, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3031 (p : Pattern) (guard : d984 p = 1) : d315 p ≤ (0 : Int) + d375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d315, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3017 p hg
    simpa only [d315, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d315, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3030 p hg
    simpa only [d315, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3032 (p : Pattern) (guard : d984 p = 1) : d316 p ≤ (0 : Int) + d376 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d316, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3005 p hg
    simpa only [d316, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d316, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3031 p hg
    simpa only [d316, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3033 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d329 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3034 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d298, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3033 p hg
    simpa only [d984, d298, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3035 (p : Pattern) (guard : d984 p = 1) : d299 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d299, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2975 p hg
    simpa only [d299, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d299, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3034 p hg
    simpa only [d299, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3036 (p : Pattern) (guard : d984 p = 1) : d300 p ≤ (0 : Int) + d331 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2978 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3037 (p : Pattern) (guard : d984 p = 1) : d301 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d301, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3036 p hg
    simpa only [d301, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d301, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2989 p hg
    simpa only [d301, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3038 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3039 (p : Pattern) (guard : d984 p = 1) : d298 p ≤ (0 : Int) + d328 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3038 p hg
    simpa only [d984, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3040 (p : Pattern) (guard : d984 p = 1) : d317 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d317, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d984, d317, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d317, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d984, d317, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3041 (p : Pattern) (guard : d984 p = 1) : d318 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d318, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3039 p hg
    simpa only [d318, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d318, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3040 p hg
    simpa only [d318, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3042 (p : Pattern) (guard : d984 p = 1) : d319 p ≤ (0 : Int) + d347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2996 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3043 (p : Pattern) (guard : d984 p = 1) : d320 p ≤ (0 : Int) + d377 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d320, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3042 p hg
    simpa only [d320, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d320, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3003 p hg
    simpa only [d320, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3044 (p : Pattern) (guard : d984 p = 1) : d321 p ≤ (0 : Int) + d378 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d321, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3037 p hg
    simpa only [d321, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d321, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3043 p hg
    simpa only [d321, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3045 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3046 (p : Pattern) (guard : d984 p = 1) : d309 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d309, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d984, d309, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d309, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3045 p hg
    simpa only [d984, d309, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3047 (p : Pattern) (guard : d984 p = 1) : d310 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d310, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3019 p hg
    simpa only [d310, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d310, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3046 p hg
    simpa only [d310, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3048 (p : Pattern) (guard : d984 p = 1) : d311 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d311, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3035 p hg
    simpa only [d311, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d311, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3047 p hg
    simpa only [d311, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3049 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d379 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d312, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d984, d312, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d312, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2998 p hg
    simpa only [d984, d312, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3050 (p : Pattern) (guard : d984 p = 1) : d312 p ≤ (0 : Int) + d380 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3026 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3049 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3051 (p : Pattern) (guard : d984 p = 1) : d313 p ≤ (0 : Int) + d381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d313, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3016 p hg
    simpa only [d313, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d313, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3050 p hg
    simpa only [d313, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3052 (p : Pattern) (guard : d984 p = 1) : d314 p ≤ (0 : Int) + d382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d314, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3048 p hg
    simpa only [d314, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d314, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3051 p hg
    simpa only [d314, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3053 (p : Pattern) (guard : d984 p = 1) : d322 p ≤ (0 : Int) + d383 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d322, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3041 p hg
    simpa only [d322, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d322, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d322, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3054 (p : Pattern) (guard : d984 p = 1) : d323 p ≤ (0 : Int) + d384 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d323, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3028 p hg
    simpa only [d323, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d323, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d323, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3055 (p : Pattern) (guard : d984 p = 1) : d324 p ≤ (0 : Int) + d385 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d324, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3053 p hg
    simpa only [d324, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d324, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3054 p hg
    simpa only [d324, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3056 (p : Pattern) (guard : d984 p = 1) : d325 p ≤ (0 : Int) + d386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d325, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3052 p hg
    simpa only [d325, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d325, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3055 p hg
    simpa only [d325, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3057 (p : Pattern) (guard : d984 p = 1) : d326 p ≤ (0 : Int) + d387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d326, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3044 p hg
    simpa only [d326, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d326, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3056 p hg
    simpa only [d326, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3058 (p : Pattern) (guard : d984 p = 1) : d327 p ≤ (0 : Int) + d388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d327, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3032 p hg
    simpa only [d327, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d327, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3057 p hg
    simpa only [d327, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3059 (p : Pattern) (guard : d914 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare3060 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3061 (p : Pattern) (guard : d1175 p = 1) : d293 p ≤ (0 : Int) + d16 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3060 p hg
    simpa only [d1175, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3062 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3063 (p : Pattern) (guard : d1175 p = 1) : d293 p ≤ (0 : Int) + d1176 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d293, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d293, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d293, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3062 p hg
    simpa only [d1175, d293, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3064 (p : Pattern) (guard : d1175 p = 1) : d293 p ≤ (0 : Int) + d1177 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3061 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3063 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3065 (p : Pattern) (guard : d914 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  omega
theorem compare3066 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3067 (p : Pattern) (guard : d1175 p = 1) : d294 p ≤ (0 : Int) + d15 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d1175, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3066 p hg
    simpa only [d1175, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3068 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3069 (p : Pattern) (guard : d1175 p = 1) : d294 p ≤ (0 : Int) + d1178 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d294, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3065 p hg
    simpa only [d1175, d294, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d294, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3068 p hg
    simpa only [d1175, d294, d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3070 (p : Pattern) (guard : d1175 p = 1) : d294 p ≤ (0 : Int) + d1179 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3067 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3069 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3071 (p : Pattern) (guard : d914 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  omega
theorem compare3072 (p : Pattern) (guard : d1175 p = 1) : d295 p ≤ (0 : Int) + d53 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d1175, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d1175, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3073 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3074 (p : Pattern) (guard : d1175 p = 1) : d295 p ≤ (0 : Int) + d1180 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d295, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3071 p hg
    simpa only [d1175, d295, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d295, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3073 p hg
    simpa only [d1175, d295, d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3075 (p : Pattern) (guard : d1175 p = 1) : d295 p ≤ (0 : Int) + d1181 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3076 (p : Pattern) (guard : d1175 p = 1) : d296 p ≤ (0 : Int) + d1182 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d296, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3070 p hg
    simpa only [d296, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d296, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3075 p hg
    simpa only [d296, d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3077 (p : Pattern) (guard : d1175 p = 1) : d297 p ≤ (0 : Int) + d1183 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d297, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3064 p hg
    simpa only [d297, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d297, d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3076 p hg
    simpa only [d297, d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3078 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3079 (p : Pattern) (guard : d1175 p = 1) : d293 p ≤ (0 : Int) + d1184 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d293, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3059 p hg
    simpa only [d1175, d293, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d293, d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3078 p hg
    simpa only [d1175, d293, d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
