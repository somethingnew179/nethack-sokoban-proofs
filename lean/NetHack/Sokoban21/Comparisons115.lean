/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons114
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16100 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d2784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16099 pattern childGuard
    simpa only [d544, d2784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16011 pattern childGuard
    simpa only [d544, d2784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16101 (pattern : Twelve) (guard : d2746 pattern = 1) : d582 pattern ≤ (1 : Int) + d2785 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d582, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16070 pattern childGuard
    simpa only [d582, d2785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d582, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16100 pattern childGuard
    simpa only [d582, d2785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16102 (pattern : Twelve) (guard : d2746 pattern = 1) : d583 pattern ≤ (1 : Int) + d2786 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d583, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d583, d2786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d583, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16096 pattern childGuard
    simpa only [d583, d2786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16103 (pattern : Twelve) (guard : d2746 pattern = 1) : d602 pattern ≤ (1 : Int) + d2787 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d602, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16101 pattern childGuard
    simpa only [d602, d2787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d602, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16102 pattern childGuard
    simpa only [d602, d2787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16104 (pattern : Twelve) (guard : d2746 pattern = 1) : d614 pattern ≤ (1 : Int) + d2788 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d614, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16098 pattern childGuard
    simpa only [d614, d2788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d614, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16103 pattern childGuard
    simpa only [d614, d2788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16105 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d2785 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d2785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16100 pattern childGuard
    simpa only [d2785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16106 (pattern : Twelve) (guard : d2746 pattern = 1) : d603 pattern ≤ (1 : Int) + d2787 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d603, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16105 pattern childGuard
    simpa only [d603, d2787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d603, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16102 pattern childGuard
    simpa only [d603, d2787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16107 (pattern : Twelve) (guard : d2746 pattern = 1) : d615 pattern ≤ (1 : Int) + d2788 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d615, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16098 pattern childGuard
    simpa only [d615, d2788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d615, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16106 pattern childGuard
    simpa only [d615, d2788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16108 (pattern : Twelve) (guard : d2746 pattern = 1) : d622 pattern ≤ (1 : Int) + d2788 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16104 pattern childGuard
    simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16107 pattern childGuard
    simpa only [d622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16109 (pattern : Twelve) (guard : d2746 pattern = 1) : d527 pattern ≤ (1 : Int) + d2789 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d527, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d527, d2789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d527, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16034 pattern childGuard
    simpa only [d527, d2789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16110 (pattern : Twelve) (guard : d2746 pattern = 1) : d558 pattern ≤ (1 : Int) + d2790 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d558, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16099 pattern childGuard
    simpa only [d558, d2790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d558, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16109 pattern childGuard
    simpa only [d558, d2790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16111 (pattern : Twelve) (guard : d2746 pattern = 1) : d584 pattern ≤ (1 : Int) + d2791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d584, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d584, d2791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d584, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16110 pattern childGuard
    simpa only [d584, d2791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16112 (pattern : Twelve) (guard : d2746 pattern = 1) : d518 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16025 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16113 (pattern : Twelve) (guard : d2746 pattern = 1) : d556 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16112 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16114 (pattern : Twelve) (guard : d2746 pattern = 1) : d585 pattern ≤ (1 : Int) + d2792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d585, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16113 pattern childGuard
    simpa only [d585, d2792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d585, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16096 pattern childGuard
    simpa only [d585, d2792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16115 (pattern : Twelve) (guard : d2746 pattern = 1) : d604 pattern ≤ (1 : Int) + d2793 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d604, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16111 pattern childGuard
    simpa only [d604, d2793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d604, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16114 pattern childGuard
    simpa only [d604, d2793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16116 (pattern : Twelve) (guard : d2746 pattern = 1) : d497 pattern ≤ (1 : Int) + d497 pattern := by
  omega
theorem c16117 (pattern : Twelve) (guard : d2746 pattern = 1) : d528 pattern ≤ (1 : Int) + d2794 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d528, d2794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16116 pattern childGuard
    simpa only [d528, d2794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16118 (pattern : Twelve) (guard : d2746 pattern = 1) : d492 pattern ≤ (1 : Int) + d2795 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d492, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16024 pattern childGuard
    simpa only [d2746, d492, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d492, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11128 pattern childGuard
    simpa only [d2746, d492, d2795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16119 (pattern : Twelve) (guard : d2746 pattern = 1) : d529 pattern ≤ (1 : Int) + d2796 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d529, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16118 pattern childGuard
    simpa only [d529, d2796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d529, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d529, d2796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16120 (pattern : Twelve) (guard : d2746 pattern = 1) : d559 pattern ≤ (1 : Int) + d2797 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16117 pattern childGuard
    simpa only [d559, d2797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16119 pattern childGuard
    simpa only [d559, d2797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16121 (pattern : Twelve) (guard : d2746 pattern = 1) : d586 pattern ≤ (1 : Int) + d2798 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d586, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16042 pattern childGuard
    simpa only [d586, d2798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d586, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16120 pattern childGuard
    simpa only [d586, d2798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16122 (pattern : Twelve) (guard : d7 pattern = 1) : d5 pattern ≤ (1 : Int) + d5 pattern := by
  omega
theorem c16123 (pattern : Twelve) (guard : d2746 pattern = 1) : d497 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16122 pattern childGuard
    simpa only [d2746, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d2746, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16124 (pattern : Twelve) (guard : d2746 pattern = 1) : d528 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15975 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16123 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16125 (pattern : Twelve) (guard : d2746 pattern = 1) : d529 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16025 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16126 (pattern : Twelve) (guard : d2746 pattern = 1) : d559 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16124 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16125 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16127 (pattern : Twelve) (guard : d2746 pattern = 1) : d530 pattern ≤ (1 : Int) + d2752 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d530, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d530, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d530, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d530, d2752, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16128 (pattern : Twelve) (guard : d2746 pattern = 1) : d531 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15972 pattern childGuard
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16129 (pattern : Twelve) (guard : d2746 pattern = 1) : d560 pattern ≤ (1 : Int) + d2799 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d560, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16127 pattern childGuard
    simpa only [d560, d2799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d560, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16128 pattern childGuard
    simpa only [d560, d2799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16130 (pattern : Twelve) (guard : d2746 pattern = 1) : d587 pattern ≤ (1 : Int) + d2800 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d587, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16126 pattern childGuard
    simpa only [d587, d2800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d587, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16129 pattern childGuard
    simpa only [d587, d2800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16131 (pattern : Twelve) (guard : d2746 pattern = 1) : d605 pattern ≤ (1 : Int) + d2801 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d605, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16121 pattern childGuard
    simpa only [d605, d2801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d605, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16130 pattern childGuard
    simpa only [d605, d2801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16132 (pattern : Twelve) (guard : d2746 pattern = 1) : d616 pattern ≤ (1 : Int) + d2802 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d616, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16115 pattern childGuard
    simpa only [d616, d2802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d616, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16131 pattern childGuard
    simpa only [d616, d2802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16133 (pattern : Twelve) (guard : d2746 pattern = 1) : d617 pattern ≤ (1 : Int) + d2803 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d617, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16106 pattern childGuard
    simpa only [d617, d2803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d617, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d617, d2803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16134 (pattern : Twelve) (guard : d2746 pattern = 1) : d623 pattern ≤ (1 : Int) + d2804 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d623, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16132 pattern childGuard
    simpa only [d623, d2804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d623, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16133 pattern childGuard
    simpa only [d623, d2804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16135 (pattern : Twelve) (guard : d2746 pattern = 1) : d626 pattern ≤ (1 : Int) + d2805 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d626, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16108 pattern childGuard
    simpa only [d626, d2805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d626, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16134 pattern childGuard
    simpa only [d626, d2805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16136 (pattern : Twelve) (guard : d2746 pattern = 1) : d629 pattern ≤ (1 : Int) + d2806 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d629, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16094 pattern childGuard
    simpa only [d629, d2806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d629, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16135 pattern childGuard
    simpa only [d629, d2806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16137 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16138 (pattern : Twelve) (guard : d7 pattern = 1) : d7 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16137 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11212 pattern childGuard
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16139 (pattern : Twelve) (guard : d2746 pattern = 1) : d1105 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16138 pattern childGuard
    simpa only [d2746, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d2746, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16140 (pattern : Twelve) (guard : d2746 pattern = 1) : d1108 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16139 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15944 pattern childGuard
    simpa only [d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16141 (pattern : Twelve) (guard : d2746 pattern = 1) : d1118 pattern ≤ (1 : Int) + d2807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1118, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15945 pattern childGuard
    simpa only [d1118, d2807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1118, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16140 pattern childGuard
    simpa only [d1118, d2807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16142 (pattern : Twelve) (guard : d2746 pattern = 1) : d1132 pattern ≤ (1 : Int) + d2808 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1132, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15952 pattern childGuard
    simpa only [d1132, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1132, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16141 pattern childGuard
    simpa only [d1132, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16143 (pattern : Twelve) (guard : d2746 pattern = 1) : d501 pattern ≤ (1 : Int) + d477 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15943 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16144 (pattern : Twelve) (guard : d2746 pattern = 1) : d1119 pattern ≤ (1 : Int) + d477 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16143 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16145 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16146 (pattern : Twelve) (guard : d7 pattern = 1) : d10 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16145 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11230 pattern childGuard
    simpa only [d7, d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16147 (pattern : Twelve) (guard : d2746 pattern = 1) : d482 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16146 pattern childGuard
    simpa only [d2746, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16148 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16149 (pattern : Twelve) (guard : d7 pattern = 1) : d16 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16148 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11231 pattern childGuard
    simpa only [d7, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16150 (pattern : Twelve) (guard : d2746 pattern = 1) : d495 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16149 pattern childGuard
    simpa only [d2746, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11237 pattern childGuard
    simpa only [d2746, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16151 (pattern : Twelve) (guard : d2746 pattern = 1) : d1109 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16147 pattern childGuard
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16150 pattern childGuard
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16152 (pattern : Twelve) (guard : d2746 pattern = 1) : d522 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16150 pattern childGuard
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16153 (pattern : Twelve) (guard : d2746 pattern = 1) : d1120 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16151 pattern childGuard
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16152 pattern childGuard
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16154 (pattern : Twelve) (guard : d2746 pattern = 1) : d1133 pattern ≤ (1 : Int) + d2809 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1133, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16144 pattern childGuard
    simpa only [d1133, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1133, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16153 pattern childGuard
    simpa only [d1133, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16155 (pattern : Twelve) (guard : d2746 pattern = 1) : d1152 pattern ≤ (1 : Int) + d2810 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1152, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16142 pattern childGuard
    simpa only [d1152, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1152, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16154 pattern childGuard
    simpa only [d1152, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16156 (pattern : Twelve) (guard : d2746 pattern = 1) : d1121 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15976 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16008 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16157 (pattern : Twelve) (guard : d2746 pattern = 1) : d1110 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1110, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16139 pattern childGuard
    simpa only [d1110, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1110, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1110, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16158 (pattern : Twelve) (guard : d2746 pattern = 1) : d1122 pattern ≤ (1 : Int) + d2811 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1122, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d1122, d2811, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1122, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16157 pattern childGuard
    simpa only [d1122, d2811, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16159 (pattern : Twelve) (guard : d2746 pattern = 1) : d1134 pattern ≤ (1 : Int) + d2812 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1134, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16156 pattern childGuard
    simpa only [d1134, d2812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1134, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16158 pattern childGuard
    simpa only [d1134, d2812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16160 (pattern : Twelve) (guard : d2746 pattern = 1) : d544 pattern ≤ (1 : Int) + d2813 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d544, d2813, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d544, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16011 pattern childGuard
    simpa only [d544, d2813, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16161 (pattern : Twelve) (guard : d2746 pattern = 1) : d1135 pattern ≤ (1 : Int) + d2814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1135, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16160 pattern childGuard
    simpa only [d1135, d2814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1135, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16153 pattern childGuard
    simpa only [d1135, d2814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16162 (pattern : Twelve) (guard : d2746 pattern = 1) : d1153 pattern ≤ (1 : Int) + d2815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1153, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16159 pattern childGuard
    simpa only [d1153, d2815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1153, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16161 pattern childGuard
    simpa only [d1153, d2815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16163 (pattern : Twelve) (guard : d2746 pattern = 1) : d1164 pattern ≤ (1 : Int) + d2816 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1164, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16155 pattern childGuard
    simpa only [d1164, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1164, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16162 pattern childGuard
    simpa only [d1164, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16164 (pattern : Twelve) (guard : d2746 pattern = 1) : d1123 pattern ≤ (1 : Int) + d2807 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1123, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16000 pattern childGuard
    simpa only [d1123, d2807, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1123, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16140 pattern childGuard
    simpa only [d1123, d2807, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16165 (pattern : Twelve) (guard : d2746 pattern = 1) : d1136 pattern ≤ (1 : Int) + d2808 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1136, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16003 pattern childGuard
    simpa only [d1136, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1136, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16164 pattern childGuard
    simpa only [d1136, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16166 (pattern : Twelve) (guard : d2746 pattern = 1) : d1137 pattern ≤ (1 : Int) + d2809 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1137, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1137, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1137, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16153 pattern childGuard
    simpa only [d1137, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16167 (pattern : Twelve) (guard : d2746 pattern = 1) : d1154 pattern ≤ (1 : Int) + d2810 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1154, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16165 pattern childGuard
    simpa only [d1154, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1154, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16166 pattern childGuard
    simpa only [d1154, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16168 (pattern : Twelve) (guard : d2746 pattern = 1) : d1138 pattern ≤ (1 : Int) + d2812 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1138, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d1138, d2812, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1138, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16158 pattern childGuard
    simpa only [d1138, d2812, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16169 (pattern : Twelve) (guard : d2746 pattern = 1) : d1155 pattern ≤ (1 : Int) + d2815 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1155, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16168 pattern childGuard
    simpa only [d1155, d2815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1155, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16161 pattern childGuard
    simpa only [d1155, d2815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16170 (pattern : Twelve) (guard : d2746 pattern = 1) : d1165 pattern ≤ (1 : Int) + d2816 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1165, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16167 pattern childGuard
    simpa only [d1165, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1165, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16169 pattern childGuard
    simpa only [d1165, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16171 (pattern : Twelve) (guard : d2746 pattern = 1) : d1173 pattern ≤ (1 : Int) + d2816 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16163 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16170 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16172 (pattern : Twelve) (guard : d2746 pattern = 1) : d1111 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1111, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16139 pattern childGuard
    simpa only [d1111, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1111, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16025 pattern childGuard
    simpa only [d1111, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16173 (pattern : Twelve) (guard : d2746 pattern = 1) : d1124 pattern ≤ (1 : Int) + d2817 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1124, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d1124, d2817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1124, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16172 pattern childGuard
    simpa only [d1124, d2817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16174 (pattern : Twelve) (guard : d2746 pattern = 1) : d1139 pattern ≤ (1 : Int) + d2818 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1139, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16029 pattern childGuard
    simpa only [d1139, d2818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1139, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16173 pattern childGuard
    simpa only [d1139, d2818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16175 (pattern : Twelve) (guard : d2746 pattern = 1) : d1140 pattern ≤ (1 : Int) + d2819 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1140, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d1140, d2819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1140, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16153 pattern childGuard
    simpa only [d1140, d2819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16176 (pattern : Twelve) (guard : d2746 pattern = 1) : d1156 pattern ≤ (1 : Int) + d2820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1156, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16174 pattern childGuard
    simpa only [d1156, d2820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1156, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16175 pattern childGuard
    simpa only [d1156, d2820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16177 (pattern : Twelve) (guard : d0 pattern = 1) : d2 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16178 (pattern : Twelve) (guard : d7 pattern = 1) : d9 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16177 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11190 pattern childGuard
    simpa only [d7, d9, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16179 (pattern : Twelve) (guard : d2746 pattern = 1) : d1106 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16178 pattern childGuard
    simpa only [d2746, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d2746, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16180 (pattern : Twelve) (guard : d2746 pattern = 1) : d1112 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1112, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16179 pattern childGuard
    simpa only [d1112, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1112, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1112, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16181 (pattern : Twelve) (guard : d2746 pattern = 1) : d1125 pattern ≤ (1 : Int) + d2821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1125, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16045 pattern childGuard
    simpa only [d1125, d2821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1125, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16180 pattern childGuard
    simpa only [d1125, d2821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16182 (pattern : Twelve) (guard : d2746 pattern = 1) : d1141 pattern ≤ (1 : Int) + d2822 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1141, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16042 pattern childGuard
    simpa only [d1141, d2822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1141, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16181 pattern childGuard
    simpa only [d1141, d2822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16183 (pattern : Twelve) (guard : d2746 pattern = 1) : d549 pattern ≤ (1 : Int) + d2823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16045 pattern childGuard
    simpa only [d549, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d549, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16039 pattern childGuard
    simpa only [d549, d2823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16184 (pattern : Twelve) (guard : d2746 pattern = 1) : d1113 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16150 pattern childGuard
    simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15980 pattern childGuard
    simpa only [d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16185 (pattern : Twelve) (guard : d2746 pattern = 1) : d178 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15980 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16186 (pattern : Twelve) (guard : d2746 pattern = 1) : d1126 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16184 pattern childGuard
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16185 pattern childGuard
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16187 (pattern : Twelve) (guard : d2746 pattern = 1) : d1142 pattern ≤ (1 : Int) + d2824 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1142, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16183 pattern childGuard
    simpa only [d1142, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1142, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16186 pattern childGuard
    simpa only [d1142, d2824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16188 (pattern : Twelve) (guard : d2746 pattern = 1) : d1157 pattern ≤ (1 : Int) + d2825 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1157, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16182 pattern childGuard
    simpa only [d1157, d2825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1157, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16187 pattern childGuard
    simpa only [d1157, d2825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16189 (pattern : Twelve) (guard : d2746 pattern = 1) : d1166 pattern ≤ (1 : Int) + d2826 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1166, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16176 pattern childGuard
    simpa only [d1166, d2826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1166, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16188 pattern childGuard
    simpa only [d1166, d2826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16190 (pattern : Twelve) (guard : d2746 pattern = 1) : d1167 pattern ≤ (1 : Int) + d2827 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1167, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16169 pattern childGuard
    simpa only [d1167, d2827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1167, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1167, d2827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16191 (pattern : Twelve) (guard : d2746 pattern = 1) : d1174 pattern ≤ (1 : Int) + d2828 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1174, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16189 pattern childGuard
    simpa only [d1174, d2828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1174, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16190 pattern childGuard
    simpa only [d1174, d2828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16192 (pattern : Twelve) (guard : d2746 pattern = 1) : d1177 pattern ≤ (1 : Int) + d2829 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1177, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16171 pattern childGuard
    simpa only [d1177, d2829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1177, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16191 pattern childGuard
    simpa only [d1177, d2829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16193 (pattern : Twelve) (guard : d2746 pattern = 1) : d1143 pattern ≤ (1 : Int) + d2808 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1143, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d1143, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1143, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16164 pattern childGuard
    simpa only [d1143, d2808, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16194 (pattern : Twelve) (guard : d2746 pattern = 1) : d1158 pattern ≤ (1 : Int) + d2810 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1158, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16193 pattern childGuard
    simpa only [d1158, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1158, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16166 pattern childGuard
    simpa only [d1158, d2810, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16195 (pattern : Twelve) (guard : d2746 pattern = 1) : d1168 pattern ≤ (1 : Int) + d2816 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1168, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16194 pattern childGuard
    simpa only [d1168, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1168, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16169 pattern childGuard
    simpa only [d1168, d2816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16196 (pattern : Twelve) (guard : d2746 pattern = 1) : d1144 pattern ≤ (1 : Int) + d2818 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1144, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d1144, d2818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1144, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16173 pattern childGuard
    simpa only [d1144, d2818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16197 (pattern : Twelve) (guard : d2746 pattern = 1) : d1159 pattern ≤ (1 : Int) + d2820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1159, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16196 pattern childGuard
    simpa only [d1159, d2820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1159, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16175 pattern childGuard
    simpa only [d1159, d2820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16198 (pattern : Twelve) (guard : d2746 pattern = 1) : d1169 pattern ≤ (1 : Int) + d2826 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1169, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16197 pattern childGuard
    simpa only [d1169, d2826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1169, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16188 pattern childGuard
    simpa only [d1169, d2826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16199 (pattern : Twelve) (guard : d2746 pattern = 1) : d1175 pattern ≤ (1 : Int) + d2828 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1175, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16198 pattern childGuard
    simpa only [d1175, d2828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1175, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16190 pattern childGuard
    simpa only [d1175, d2828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16200 (pattern : Twelve) (guard : d2746 pattern = 1) : d1178 pattern ≤ (1 : Int) + d2829 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1178, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16195 pattern childGuard
    simpa only [d1178, d2829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1178, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16199 pattern childGuard
    simpa only [d1178, d2829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16201 (pattern : Twelve) (guard : d2746 pattern = 1) : d1180 pattern ≤ (1 : Int) + d2829 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16192 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16200 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16202 (pattern : Twelve) (guard : d2746 pattern = 1) : d1181 pattern ≤ (1 : Int) + d2829 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16201 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16200 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16203 (pattern : Twelve) (guard : d2746 pattern = 1) : d479 pattern ≤ (1 : Int) + d2830 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d479, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15940 pattern childGuard
    simpa only [d2746, d479, d2830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d479, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11105 pattern childGuard
    simpa only [d2746, d479, d2830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16204 (pattern : Twelve) (guard : d2746 pattern = 1) : d513 pattern ≤ (1 : Int) + d2831 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d513, d2831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d513, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d513, d2831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16205 (pattern : Twelve) (guard : d2746 pattern = 1) : d1108 pattern ≤ (1 : Int) + d2832 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16139 pattern childGuard
    simpa only [d1108, d2832, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1108, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16203 pattern childGuard
    simpa only [d1108, d2832, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16206 (pattern : Twelve) (guard : d2746 pattern = 1) : d1123 pattern ≤ (1 : Int) + d2833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1123, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16204 pattern childGuard
    simpa only [d1123, d2833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1123, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16205 pattern childGuard
    simpa only [d1123, d2833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16207 (pattern : Twelve) (guard : d2746 pattern = 1) : d1143 pattern ≤ (1 : Int) + d2834 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1143, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15950 pattern childGuard
    simpa only [d1143, d2834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1143, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16206 pattern childGuard
    simpa only [d1143, d2834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16208 (pattern : Twelve) (guard : d2746 pattern = 1) : d1114 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16147 pattern childGuard
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15980 pattern childGuard
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16209 (pattern : Twelve) (guard : d2746 pattern = 1) : d1127 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16208 pattern childGuard
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16152 pattern childGuard
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16210 (pattern : Twelve) (guard : d2746 pattern = 1) : d1145 pattern ≤ (1 : Int) + d2809 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1145, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1145, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1145, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16209 pattern childGuard
    simpa only [d1145, d2809, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16211 (pattern : Twelve) (guard : d2746 pattern = 1) : d1160 pattern ≤ (1 : Int) + d2835 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1160, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16207 pattern childGuard
    simpa only [d1160, d2835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1160, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16210 pattern childGuard
    simpa only [d1160, d2835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16212 (pattern : Twelve) (guard : d2746 pattern = 1) : d1115 pattern ≤ (1 : Int) + d2762 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1115, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d1115, d2762, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1115, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16179 pattern childGuard
    simpa only [d1115, d2762, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16213 (pattern : Twelve) (guard : d2746 pattern = 1) : d1128 pattern ≤ (1 : Int) + d2836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1128, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16212 pattern childGuard
    simpa only [d1128, d2836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1128, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16157 pattern childGuard
    simpa only [d1128, d2836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16214 (pattern : Twelve) (guard : d2746 pattern = 1) : d1146 pattern ≤ (1 : Int) + d2837 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1146, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16014 pattern childGuard
    simpa only [d1146, d2837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1146, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16213 pattern childGuard
    simpa only [d1146, d2837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16215 (pattern : Twelve) (guard : d2746 pattern = 1) : d1147 pattern ≤ (1 : Int) + d2814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1147, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16160 pattern childGuard
    simpa only [d1147, d2814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1147, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16209 pattern childGuard
    simpa only [d1147, d2814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16216 (pattern : Twelve) (guard : d2746 pattern = 1) : d1161 pattern ≤ (1 : Int) + d2838 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1161, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16214 pattern childGuard
    simpa only [d1161, d2838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1161, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16215 pattern childGuard
    simpa only [d1161, d2838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16217 (pattern : Twelve) (guard : d2746 pattern = 1) : d1170 pattern ≤ (1 : Int) + d2839 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1170, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16211 pattern childGuard
    simpa only [d1170, d2839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1170, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16216 pattern childGuard
    simpa only [d1170, d2839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16218 (pattern : Twelve) (guard : d2746 pattern = 1) : d1116 pattern ≤ (1 : Int) + d2840 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1116, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16139 pattern childGuard
    simpa only [d1116, d2840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1116, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16044 pattern childGuard
    simpa only [d1116, d2840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16219 (pattern : Twelve) (guard : d2746 pattern = 1) : d1129 pattern ≤ (1 : Int) + d2841 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1129, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16212 pattern childGuard
    simpa only [d1129, d2841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1129, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16218 pattern childGuard
    simpa only [d1129, d2841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16220 (pattern : Twelve) (guard : d2746 pattern = 1) : d1148 pattern ≤ (1 : Int) + d2842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1148, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16010 pattern childGuard
    simpa only [d1148, d2842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1148, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16219 pattern childGuard
    simpa only [d1148, d2842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16221 (pattern : Twelve) (guard : d2746 pattern = 1) : d518 pattern ≤ (1 : Int) + d2843 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15977 pattern childGuard
    simpa only [d518, d2843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d518, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16118 pattern childGuard
    simpa only [d518, d2843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16222 (pattern : Twelve) (guard : d2746 pattern = 1) : d556 pattern ≤ (1 : Int) + d2844 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15990 pattern childGuard
    simpa only [d556, d2844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d556, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16221 pattern childGuard
    simpa only [d556, d2844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16223 (pattern : Twelve) (guard : d2746 pattern = 1) : d1149 pattern ≤ (1 : Int) + d2845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1149, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16222 pattern childGuard
    simpa only [d1149, d2845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1149, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16209 pattern childGuard
    simpa only [d1149, d2845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16224 (pattern : Twelve) (guard : d2746 pattern = 1) : d1162 pattern ≤ (1 : Int) + d2846 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1162, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16220 pattern childGuard
    simpa only [d1162, d2846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1162, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16223 pattern childGuard
    simpa only [d1162, d2846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16225 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (1 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16226 (pattern : Twelve) (guard : d7 pattern = 1) : d117 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16225 pattern childGuard
    simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12142 pattern childGuard
    simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16227 (pattern : Twelve) (guard : d2746 pattern = 1) : d1107 pattern ≤ (1 : Int) + d2769 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1107, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16226 pattern childGuard
    simpa only [d2746, d1107, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1107, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d2746, d1107, d2769, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16228 (pattern : Twelve) (guard : d2746 pattern = 1) : d1117 pattern ≤ (1 : Int) + d2771 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1117, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16227 pattern childGuard
    simpa only [d1117, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1117, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1117, d2771, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16229 (pattern : Twelve) (guard : d2746 pattern = 1) : d1130 pattern ≤ (1 : Int) + d2847 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1130, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16127 pattern childGuard
    simpa only [d1130, d2847, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1130, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16228 pattern childGuard
    simpa only [d1130, d2847, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16230 (pattern : Twelve) (guard : d2746 pattern = 1) : d1150 pattern ≤ (1 : Int) + d2848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1150, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16042 pattern childGuard
    simpa only [d1150, d2848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1150, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16229 pattern childGuard
    simpa only [d1150, d2848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16231 (pattern : Twelve) (guard : d2746 pattern = 1) : d528 pattern ≤ (1 : Int) + d2849 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15989 pattern childGuard
    simpa only [d528, d2849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d528, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16116 pattern childGuard
    simpa only [d528, d2849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16232 (pattern : Twelve) (guard : d2746 pattern = 1) : d559 pattern ≤ (1 : Int) + d2850 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16231 pattern childGuard
    simpa only [d559, d2850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d559, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16119 pattern childGuard
    simpa only [d559, d2850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16233 (pattern : Twelve) (guard : d2746 pattern = 1) : d1131 pattern ≤ (1 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16152 pattern childGuard
    simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16234 (pattern : Twelve) (guard : d2746 pattern = 1) : d1151 pattern ≤ (1 : Int) + d2851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1151, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16232 pattern childGuard
    simpa only [d1151, d2851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1151, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16233 pattern childGuard
    simpa only [d1151, d2851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16235 (pattern : Twelve) (guard : d2746 pattern = 1) : d1163 pattern ≤ (1 : Int) + d2852 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1163, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16230 pattern childGuard
    simpa only [d1163, d2852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1163, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16234 pattern childGuard
    simpa only [d1163, d2852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16236 (pattern : Twelve) (guard : d2746 pattern = 1) : d1171 pattern ≤ (1 : Int) + d2853 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1171, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16224 pattern childGuard
    simpa only [d1171, d2853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1171, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16235 pattern childGuard
    simpa only [d1171, d2853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16237 (pattern : Twelve) (guard : d2746 pattern = 1) : d1172 pattern ≤ (1 : Int) + d2854 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1172, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16216 pattern childGuard
    simpa only [d1172, d2854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1172, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1172, d2854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16238 (pattern : Twelve) (guard : d2746 pattern = 1) : d1176 pattern ≤ (1 : Int) + d2855 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1176, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16236 pattern childGuard
    simpa only [d1176, d2855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1176, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16237 pattern childGuard
    simpa only [d1176, d2855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16239 (pattern : Twelve) (guard : d2746 pattern = 1) : d1179 pattern ≤ (1 : Int) + d2856 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1179, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16217 pattern childGuard
    simpa only [d1179, d2856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1179, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16238 pattern childGuard
    simpa only [d1179, d2856, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
