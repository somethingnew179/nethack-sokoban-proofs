/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons119
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16800 (pattern : Twelve) (guard : d1848 pattern = 1) : d830 pattern ≤ (0 : Int) + d3051 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16712 pattern childGuard
    simpa only [d830, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16708 pattern childGuard
    simpa only [d830, d3051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16801 (pattern : Twelve) (guard : d1848 pattern = 1) : d831 pattern ≤ (0 : Int) + d2469 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d831, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11711 pattern childGuard
    simpa only [d831, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d831, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11719 pattern childGuard
    simpa only [d831, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16802 (pattern : Twelve) (guard : d1848 pattern = 1) : d845 pattern ≤ (0 : Int) + d3089 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d845, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16800 pattern childGuard
    simpa only [d845, d3089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d845, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16801 pattern childGuard
    simpa only [d845, d3089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16803 (pattern : Twelve) (guard : d1848 pattern = 1) : d856 pattern ≤ (0 : Int) + d3090 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d856, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16799 pattern childGuard
    simpa only [d856, d3090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d856, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16802 pattern childGuard
    simpa only [d856, d3090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16804 (pattern : Twelve) (guard : d1848 pattern = 1) : d862 pattern ≤ (0 : Int) + d3091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16795 pattern childGuard
    simpa only [d862, d3091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d862, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16803 pattern childGuard
    simpa only [d862, d3091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16805 (pattern : Twelve) (guard : d1848 pattern = 1) : d863 pattern ≤ (0 : Int) + d3092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d863, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16788 pattern childGuard
    simpa only [d863, d3092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d863, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d863, d3092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16806 (pattern : Twelve) (guard : d1848 pattern = 1) : d867 pattern ≤ (0 : Int) + d3093 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16804 pattern childGuard
    simpa only [d867, d3093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d867, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16805 pattern childGuard
    simpa only [d867, d3093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16807 (pattern : Twelve) (guard : d1848 pattern = 1) : d869 pattern ≤ (0 : Int) + d3094 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16789 pattern childGuard
    simpa only [d869, d3094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d869, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16806 pattern childGuard
    simpa only [d869, d3094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16808 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16809 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16808 pattern childGuard
    simpa only [d17, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16810 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16811 (pattern : Twelve) (guard : d1848 pattern = 1) : d874 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16809 pattern childGuard
    simpa only [d1848, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16810 pattern childGuard
    simpa only [d1848, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16812 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16813 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16812 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16814 (pattern : Twelve) (guard : d1848 pattern = 1) : d875 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16813 pattern childGuard
    simpa only [d1848, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16810 pattern childGuard
    simpa only [d1848, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16815 (pattern : Twelve) (guard : d1848 pattern = 1) : d882 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16811 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16814 pattern childGuard
    simpa only [d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16816 (pattern : Twelve) (guard : d1848 pattern = 1) : d890 pattern ≤ (0 : Int) + d3095 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16815 pattern childGuard
    simpa only [d890, d3095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16817 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16664 pattern childGuard
    simpa only [d10, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d10, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16818 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16722 pattern childGuard
    simpa only [d11, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d11, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16819 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16817 pattern childGuard
    simpa only [d19, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16818 pattern childGuard
    simpa only [d19, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16820 (pattern : Twelve) (guard : d1848 pattern = 1) : d876 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16819 pattern childGuard
    simpa only [d1848, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11710 pattern childGuard
    simpa only [d1848, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16821 (pattern : Twelve) (guard : d1848 pattern = 1) : d883 pattern ≤ (0 : Int) + d2469 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16820 pattern childGuard
    simpa only [d883, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16713 pattern childGuard
    simpa only [d883, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16822 (pattern : Twelve) (guard : d1848 pattern = 1) : d891 pattern ≤ (0 : Int) + d3096 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16821 pattern childGuard
    simpa only [d891, d3096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16823 (pattern : Twelve) (guard : d1848 pattern = 1) : d898 pattern ≤ (0 : Int) + d3097 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16816 pattern childGuard
    simpa only [d898, d3097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16822 pattern childGuard
    simpa only [d898, d3097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16824 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16729 pattern childGuard
    simpa only [d17, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16696 pattern childGuard
    simpa only [d17, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16825 (pattern : Twelve) (guard : d0 pattern = 1) : d815 pattern ≤ (0 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16826 (pattern : Twelve) (guard : d1848 pattern = 1) : d877 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16824 pattern childGuard
    simpa only [d1848, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16825 pattern childGuard
    simpa only [d1848, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16827 (pattern : Twelve) (guard : d1848 pattern = 1) : d884 pattern ≤ (0 : Int) + d3098 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16826 pattern childGuard
    simpa only [d884, d3098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16783 pattern childGuard
    simpa only [d884, d3098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16828 (pattern : Twelve) (guard : d1848 pattern = 1) : d892 pattern ≤ (0 : Int) + d3099 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16686 pattern childGuard
    simpa only [d892, d3099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16827 pattern childGuard
    simpa only [d892, d3099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16829 (pattern : Twelve) (guard : d1848 pattern = 1) : d893 pattern ≤ (0 : Int) + d3100 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16786 pattern childGuard
    simpa only [d893, d3100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16821 pattern childGuard
    simpa only [d893, d3100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16830 (pattern : Twelve) (guard : d1848 pattern = 1) : d899 pattern ≤ (0 : Int) + d3101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16828 pattern childGuard
    simpa only [d899, d3101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16829 pattern childGuard
    simpa only [d899, d3101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16831 (pattern : Twelve) (guard : d1848 pattern = 1) : d902 pattern ≤ (0 : Int) + d3102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16823 pattern childGuard
    simpa only [d902, d3102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d902, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16830 pattern childGuard
    simpa only [d902, d3102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16832 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16741 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16722 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16833 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16742 pattern childGuard
    simpa only [d814, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16832 pattern childGuard
    simpa only [d814, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16834 (pattern : Twelve) (guard : d1848 pattern = 1) : d878 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16833 pattern childGuard
    simpa only [d1848, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16711 pattern childGuard
    simpa only [d1848, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16835 (pattern : Twelve) (guard : d1848 pattern = 1) : d885 pattern ≤ (0 : Int) + d3103 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16826 pattern childGuard
    simpa only [d885, d3103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16834 pattern childGuard
    simpa only [d885, d3103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16836 (pattern : Twelve) (guard : d1848 pattern = 1) : d894 pattern ≤ (0 : Int) + d3104 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11483 pattern childGuard
    simpa only [d894, d3104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16835 pattern childGuard
    simpa only [d894, d3104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16837 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16741 pattern childGuard
    simpa only [d7, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16838 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16837 pattern childGuard
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16839 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16840 (pattern : Twelve) (guard : d1848 pattern = 1) : d879 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16838 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16839 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16841 (pattern : Twelve) (guard : d1848 pattern = 1) : d886 pattern ≤ (0 : Int) + d2445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16840 pattern childGuard
    simpa only [d886, d2445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16842 (pattern : Twelve) (guard : d1848 pattern = 1) : d895 pattern ≤ (0 : Int) + d3105 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16841 pattern childGuard
    simpa only [d895, d3105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16821 pattern childGuard
    simpa only [d895, d3105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16843 (pattern : Twelve) (guard : d1848 pattern = 1) : d900 pattern ≤ (0 : Int) + d3106 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16836 pattern childGuard
    simpa only [d900, d3106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16842 pattern childGuard
    simpa only [d900, d3106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16844 (pattern : Twelve) (guard : d1 pattern = 1) : d15 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10946 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16845 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16756 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16844 pattern childGuard
    simpa only [d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16846 (pattern : Twelve) (guard : d1848 pattern = 1) : d880 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16845 pattern childGuard
    simpa only [d1848, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16847 (pattern : Twelve) (guard : d1848 pattern = 1) : d887 pattern ≤ (0 : Int) + d3074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d887, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16766 pattern childGuard
    simpa only [d887, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d887, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16846 pattern childGuard
    simpa only [d887, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16848 (pattern : Twelve) (guard : d1848 pattern = 1) : d896 pattern ≤ (0 : Int) + d3107 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d896, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16707 pattern childGuard
    simpa only [d896, d3107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d896, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16847 pattern childGuard
    simpa only [d896, d3107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16849 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d9, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16850 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d23, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16849 pattern childGuard
    simpa only [d23, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16851 (pattern : Twelve) (guard : d1848 pattern = 1) : d881 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16850 pattern childGuard
    simpa only [d1848, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16754 pattern childGuard
    simpa only [d1848, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16852 (pattern : Twelve) (guard : d1848 pattern = 1) : d888 pattern ≤ (0 : Int) + d3071 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d888, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16851 pattern childGuard
    simpa only [d888, d3071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d888, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16758 pattern childGuard
    simpa only [d888, d3071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16853 (pattern : Twelve) (guard : d1848 pattern = 1) : d889 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16713 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16854 (pattern : Twelve) (guard : d1848 pattern = 1) : d897 pattern ≤ (0 : Int) + d3108 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d897, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16852 pattern childGuard
    simpa only [d897, d3108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d897, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16853 pattern childGuard
    simpa only [d897, d3108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16855 (pattern : Twelve) (guard : d1848 pattern = 1) : d901 pattern ≤ (0 : Int) + d3109 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d901, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16848 pattern childGuard
    simpa only [d901, d3109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d901, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16854 pattern childGuard
    simpa only [d901, d3109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16856 (pattern : Twelve) (guard : d1848 pattern = 1) : d903 pattern ≤ (0 : Int) + d3110 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d903, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16843 pattern childGuard
    simpa only [d903, d3110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d903, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16855 pattern childGuard
    simpa only [d903, d3110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16857 (pattern : Twelve) (guard : d1848 pattern = 1) : d904 pattern ≤ (0 : Int) + d3111 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d904, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16830 pattern childGuard
    simpa only [d904, d3111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d904, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d904, d3111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16858 (pattern : Twelve) (guard : d1848 pattern = 1) : d905 pattern ≤ (0 : Int) + d3112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d905, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16856 pattern childGuard
    simpa only [d905, d3112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d905, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16857 pattern childGuard
    simpa only [d905, d3112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16859 (pattern : Twelve) (guard : d1848 pattern = 1) : d906 pattern ≤ (0 : Int) + d3113 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d906, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16831 pattern childGuard
    simpa only [d906, d3113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d906, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16858 pattern childGuard
    simpa only [d906, d3113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16860 (pattern : Twelve) (guard : d1848 pattern = 1) : d907 pattern ≤ (0 : Int) + d3114 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d907, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16807 pattern childGuard
    simpa only [d907, d3114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d907, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16859 pattern childGuard
    simpa only [d907, d3114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16861 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10901 pattern childGuard
    simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2846 pattern childGuard
    simpa only [d1275, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16862 (pattern : Twelve) (guard : d1848 pattern = 1) : d1278 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16861 pattern childGuard
    simpa only [d1848, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16810 pattern childGuard
    simpa only [d1848, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16863 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16862 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11636 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16864 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1976 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16863 pattern childGuard
    simpa only [d1293, d1976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16865 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1977 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16864 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4816 pattern childGuard
    simpa only [d1305, d1977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16866 (pattern : Twelve) (guard : d0 pattern = 1) : d1276 pattern ≤ (0 : Int) + d1276 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16867 (pattern : Twelve) (guard : d1848 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10994 pattern childGuard
    simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16866 pattern childGuard
    simpa only [d1848, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16868 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16869 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16868 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16870 (pattern : Twelve) (guard : d1848 pattern = 1) : d1280 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16869 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16871 (pattern : Twelve) (guard : d1848 pattern = 1) : d1285 pattern ≤ (0 : Int) + d3115 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16867 pattern childGuard
    simpa only [d1285, d3115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16870 pattern childGuard
    simpa only [d1285, d3115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16872 (pattern : Twelve) (guard : d1848 pattern = 1) : d1295 pattern ≤ (0 : Int) + d3116 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16786 pattern childGuard
    simpa only [d1295, d3116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16871 pattern childGuard
    simpa only [d1295, d3116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16873 (pattern : Twelve) (guard : d1848 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1286, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16657 pattern childGuard
    simpa only [d1286, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16874 (pattern : Twelve) (guard : d1848 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1694 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16873 pattern childGuard
    simpa only [d1296, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1296, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16875 (pattern : Twelve) (guard : d1848 pattern = 1) : d1306 pattern ≤ (0 : Int) + d3117 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16872 pattern childGuard
    simpa only [d1306, d3117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16874 pattern childGuard
    simpa only [d1306, d3117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16876 (pattern : Twelve) (guard : d1848 pattern = 1) : d1313 pattern ≤ (0 : Int) + d3118 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16865 pattern childGuard
    simpa only [d1313, d3118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1313, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16875 pattern childGuard
    simpa only [d1313, d3118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16877 (pattern : Twelve) (guard : d1848 pattern = 1) : d1281 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10987 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16839 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16878 (pattern : Twelve) (guard : d1848 pattern = 1) : d1287 pattern ≤ (0 : Int) + d2392 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16867 pattern childGuard
    simpa only [d1287, d2392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16877 pattern childGuard
    simpa only [d1287, d2392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16879 (pattern : Twelve) (guard : d1848 pattern = 1) : d1297 pattern ≤ (0 : Int) + d2454 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d1297, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16878 pattern childGuard
    simpa only [d1297, d2454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16880 (pattern : Twelve) (guard : d1848 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1298, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16881 (pattern : Twelve) (guard : d1848 pattern = 1) : d1307 pattern ≤ (0 : Int) + d2455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16879 pattern childGuard
    simpa only [d1307, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16880 pattern childGuard
    simpa only [d1307, d2455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16882 (pattern : Twelve) (guard : d0 pattern = 1) : d1277 pattern ≤ (0 : Int) + d1277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16883 (pattern : Twelve) (guard : d1848 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10996 pattern childGuard
    simpa only [d1848, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16882 pattern childGuard
    simpa only [d1848, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16884 (pattern : Twelve) (guard : d1848 pattern = 1) : d1288 pattern ≤ (0 : Int) + d3119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1288, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16883 pattern childGuard
    simpa only [d1288, d3119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1288, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16758 pattern childGuard
    simpa only [d1288, d3119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16885 (pattern : Twelve) (guard : d1848 pattern = 1) : d1299 pattern ≤ (0 : Int) + d3120 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1299, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16800 pattern childGuard
    simpa only [d1299, d3120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1299, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16884 pattern childGuard
    simpa only [d1299, d3120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16886 (pattern : Twelve) (guard : d1848 pattern = 1) : d1289 pattern ≤ (0 : Int) + d2469 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11711 pattern childGuard
    simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16713 pattern childGuard
    simpa only [d1289, d2469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16887 (pattern : Twelve) (guard : d1848 pattern = 1) : d1300 pattern ≤ (0 : Int) + d2470 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16886 pattern childGuard
    simpa only [d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1300, d2470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16888 (pattern : Twelve) (guard : d1848 pattern = 1) : d1308 pattern ≤ (0 : Int) + d3121 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1308, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16885 pattern childGuard
    simpa only [d1308, d3121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1308, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16887 pattern childGuard
    simpa only [d1308, d3121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16889 (pattern : Twelve) (guard : d1848 pattern = 1) : d1314 pattern ≤ (0 : Int) + d3122 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1314, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16881 pattern childGuard
    simpa only [d1314, d3122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1314, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16888 pattern childGuard
    simpa only [d1314, d3122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16890 (pattern : Twelve) (guard : d1848 pattern = 1) : d1315 pattern ≤ (0 : Int) + d3123 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1315, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16875 pattern childGuard
    simpa only [d1315, d3123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1315, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1315, d3123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16891 (pattern : Twelve) (guard : d1848 pattern = 1) : d1319 pattern ≤ (0 : Int) + d3124 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1319, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16889 pattern childGuard
    simpa only [d1319, d3124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1319, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16890 pattern childGuard
    simpa only [d1319, d3124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16892 (pattern : Twelve) (guard : d1848 pattern = 1) : d1321 pattern ≤ (0 : Int) + d3125 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16876 pattern childGuard
    simpa only [d1321, d3125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1321, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16891 pattern childGuard
    simpa only [d1321, d3125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16893 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16894 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10865 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10874 pattern childGuard
    simpa only [d8, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16895 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16893 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16894 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16896 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1324 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16897 (pattern : Twelve) (guard : d1848 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16895 pattern childGuard
    simpa only [d1848, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16896 pattern childGuard
    simpa only [d1848, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16898 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10867 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16899 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16898 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16894 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16900 (pattern : Twelve) (guard : d1848 pattern = 1) : d1326 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16899 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16896 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16901 (pattern : Twelve) (guard : d1848 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16897 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16900 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16902 (pattern : Twelve) (guard : d1848 pattern = 1) : d1339 pattern ≤ (0 : Int) + d3126 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1339, d3126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16901 pattern childGuard
    simpa only [d1339, d3126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16903 (pattern : Twelve) (guard : d1848 pattern = 1) : d1345 pattern ≤ (0 : Int) + d3127 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16902 pattern childGuard
    simpa only [d1345, d3127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4816 pattern childGuard
    simpa only [d1345, d3127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16904 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16696 pattern childGuard
    simpa only [d1275, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10984 pattern childGuard
    simpa only [d1275, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16905 (pattern : Twelve) (guard : d1848 pattern = 1) : d1327 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16904 pattern childGuard
    simpa only [d1848, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16839 pattern childGuard
    simpa only [d1848, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16906 (pattern : Twelve) (guard : d1848 pattern = 1) : d1334 pattern ≤ (0 : Int) + d3128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16905 pattern childGuard
    simpa only [d1334, d3128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16870 pattern childGuard
    simpa only [d1334, d3128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16907 (pattern : Twelve) (guard : d1848 pattern = 1) : d1340 pattern ≤ (0 : Int) + d3129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16786 pattern childGuard
    simpa only [d1340, d3129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16906 pattern childGuard
    simpa only [d1340, d3129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16908 (pattern : Twelve) (guard : d1848 pattern = 1) : d1346 pattern ≤ (0 : Int) + d3130 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16907 pattern childGuard
    simpa only [d1346, d3130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16874 pattern childGuard
    simpa only [d1346, d3130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16909 (pattern : Twelve) (guard : d1848 pattern = 1) : d1349 pattern ≤ (0 : Int) + d3131 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16903 pattern childGuard
    simpa only [d1349, d3131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1349, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16908 pattern childGuard
    simpa only [d1349, d3131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16910 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16722 pattern childGuard
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16911 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16832 pattern childGuard
    simpa only [d872, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16910 pattern childGuard
    simpa only [d872, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16912 (pattern : Twelve) (guard : d1848 pattern = 1) : d1328 pattern ≤ (0 : Int) + d1277 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16911 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16882 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16913 (pattern : Twelve) (guard : d1848 pattern = 1) : d1335 pattern ≤ (0 : Int) + d3132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16905 pattern childGuard
    simpa only [d1335, d3132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16912 pattern childGuard
    simpa only [d1335, d3132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16914 (pattern : Twelve) (guard : d1848 pattern = 1) : d1341 pattern ≤ (0 : Int) + d3133 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11577 pattern childGuard
    simpa only [d1341, d3133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16913 pattern childGuard
    simpa only [d1341, d3133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16915 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16661 pattern childGuard
    simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d10, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16916 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16741 pattern childGuard
    simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d11, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16917 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16915 pattern childGuard
    simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16916 pattern childGuard
    simpa only [d19, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16918 (pattern : Twelve) (guard : d1848 pattern = 1) : d1329 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16917 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11706 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16919 (pattern : Twelve) (guard : d1848 pattern = 1) : d1336 pattern ≤ (0 : Int) + d2461 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11655 pattern childGuard
    simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16918 pattern childGuard
    simpa only [d1336, d2461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16920 (pattern : Twelve) (guard : d1848 pattern = 1) : d1342 pattern ≤ (0 : Int) + d2462 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16919 pattern childGuard
    simpa only [d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1342, d2462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16921 (pattern : Twelve) (guard : d1848 pattern = 1) : d1347 pattern ≤ (0 : Int) + d3134 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16914 pattern childGuard
    simpa only [d1347, d3134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16920 pattern childGuard
    simpa only [d1347, d3134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16922 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15042 pattern childGuard
    simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16756 pattern childGuard
    simpa only [d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16923 (pattern : Twelve) (guard : d1848 pattern = 1) : d1330 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16922 pattern childGuard
    simpa only [d1848, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16924 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16844 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11038 pattern childGuard
    simpa only [d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16925 (pattern : Twelve) (guard : d1848 pattern = 1) : d1331 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16924 pattern childGuard
    simpa only [d1848, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16926 (pattern : Twelve) (guard : d1848 pattern = 1) : d1337 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16923 pattern childGuard
    simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16925 pattern childGuard
    simpa only [d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16927 (pattern : Twelve) (guard : d1848 pattern = 1) : d1343 pattern ≤ (0 : Int) + d3135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1343, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16800 pattern childGuard
    simpa only [d1343, d3135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1343, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16926 pattern childGuard
    simpa only [d1343, d3135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16928 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16751 pattern childGuard
    simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10944 pattern childGuard
    simpa only [d16, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16929 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16928 pattern childGuard
    simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15096 pattern childGuard
    simpa only [d25, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16930 (pattern : Twelve) (guard : d1848 pattern = 1) : d1332 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16929 pattern childGuard
    simpa only [d1848, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16676 pattern childGuard
    simpa only [d1848, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16931 (pattern : Twelve) (guard : d1848 pattern = 1) : d1338 pattern ≤ (0 : Int) + d3074 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1338, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16930 pattern childGuard
    simpa only [d1338, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1338, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16768 pattern childGuard
    simpa only [d1338, d3074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16932 (pattern : Twelve) (guard : d1848 pattern = 1) : d1344 pattern ≤ (0 : Int) + d3136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1344, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16931 pattern childGuard
    simpa only [d1344, d3136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1344, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1344, d3136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16933 (pattern : Twelve) (guard : d1848 pattern = 1) : d1348 pattern ≤ (0 : Int) + d3137 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1348, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16927 pattern childGuard
    simpa only [d1348, d3137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1348, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16932 pattern childGuard
    simpa only [d1348, d3137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16934 (pattern : Twelve) (guard : d1848 pattern = 1) : d1350 pattern ≤ (0 : Int) + d3138 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1350, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16921 pattern childGuard
    simpa only [d1350, d3138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1350, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16933 pattern childGuard
    simpa only [d1350, d3138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16935 (pattern : Twelve) (guard : d1848 pattern = 1) : d1351 pattern ≤ (0 : Int) + d3139 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1351, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16908 pattern childGuard
    simpa only [d1351, d3139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1351, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1351, d3139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16936 (pattern : Twelve) (guard : d1848 pattern = 1) : d1352 pattern ≤ (0 : Int) + d3140 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1352, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16934 pattern childGuard
    simpa only [d1352, d3140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1352, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16935 pattern childGuard
    simpa only [d1352, d3140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16937 (pattern : Twelve) (guard : d1848 pattern = 1) : d1353 pattern ≤ (0 : Int) + d3141 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1353, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16909 pattern childGuard
    simpa only [d1353, d3141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1353, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16936 pattern childGuard
    simpa only [d1353, d3141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16938 (pattern : Twelve) (guard : d1848 pattern = 1) : d1354 pattern ≤ (0 : Int) + d3142 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1354, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16892 pattern childGuard
    simpa only [d1354, d3142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1354, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16937 pattern childGuard
    simpa only [d1354, d3142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16939 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16655 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15095 pattern childGuard
    simpa only [d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
