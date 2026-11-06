/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons020
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2940 (pattern : Twelve) (guard : d1865 pattern = 1) : d60 pattern ≤ (0 : Int) + d549 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d60, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2938 pattern childGuard
    simpa only [d60, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d60, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2939 pattern childGuard
    simpa only [d60, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2941 (pattern : Twelve) (guard : d1865 pattern = 1) : d81 pattern ≤ (0 : Int) + d571 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2937 pattern childGuard
    simpa only [d81, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2940 pattern childGuard
    simpa only [d81, d571, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2942 (pattern : Twelve) (guard : d1865 pattern = 1) : d59 pattern ≤ (0 : Int) + d549 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d59, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2938 pattern childGuard
    simpa only [d59, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d59, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2936 pattern childGuard
    simpa only [d59, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2943 (pattern : Twelve) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2944 (pattern : Twelve) (guard : d1865 pattern = 1) : d24 pattern ≤ (0 : Int) + d494 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d24, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2933 pattern childGuard
    simpa only [d1865, d24, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d24, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2943 pattern childGuard
    simpa only [d1865, d24, d494, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2945 (pattern : Twelve) (guard : d1865 pattern = 1) : d41 pattern ≤ (0 : Int) + d521 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d41, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d41, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d41, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2944 pattern childGuard
    simpa only [d41, d521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2946 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (0 : Int) + d16 pattern := by
  omega
theorem c2947 (pattern : Twelve) (guard : d0 pattern = 1) : d12 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2948 (pattern : Twelve) (guard : d1865 pattern = 1) : d25 pattern ≤ (0 : Int) + d495 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d25, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2946 pattern childGuard
    simpa only [d1865, d25, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d25, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2947 pattern childGuard
    simpa only [d1865, d25, d495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2949 (pattern : Twelve) (guard : d1865 pattern = 1) : d42 pattern ≤ (0 : Int) + d522 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d42, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d42, d522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d42, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d42, d522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2950 (pattern : Twelve) (guard : d1865 pattern = 1) : d61 pattern ≤ (0 : Int) + d550 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d61, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2945 pattern childGuard
    simpa only [d61, d550, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d61, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2949 pattern childGuard
    simpa only [d61, d550, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2951 (pattern : Twelve) (guard : d1865 pattern = 1) : d82 pattern ≤ (0 : Int) + d572 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d82, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d82, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d82, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2950 pattern childGuard
    simpa only [d82, d572, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2952 (pattern : Twelve) (guard : d1865 pattern = 1) : d96 pattern ≤ (0 : Int) + d593 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2941 pattern childGuard
    simpa only [d96, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2951 pattern childGuard
    simpa only [d96, d593, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2953 (pattern : Twelve) (guard : d1865 pattern = 1) : d104 pattern ≤ (0 : Int) + d608 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2930 pattern childGuard
    simpa only [d104, d608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2952 pattern childGuard
    simpa only [d104, d608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2954 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d14 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2955 (pattern : Twelve) (guard : d1865 pattern = 1) : d0 pattern ≤ (0 : Int) + d496 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2954 pattern childGuard
    simpa only [d1865, d496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2956 (pattern : Twelve) (guard : d1865 pattern = 1) : d30 pattern ≤ (0 : Int) + d523 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2955 pattern childGuard
    simpa only [d30, d523, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d30, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d30, d523, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2957 (pattern : Twelve) (guard : d1865 pattern = 1) : d56 pattern ≤ (0 : Int) + d551 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2956 pattern childGuard
    simpa only [d56, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2904 pattern childGuard
    simpa only [d56, d551, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2958 (pattern : Twelve) (guard : d1865 pattern = 1) : d77 pattern ≤ (0 : Int) + d573 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2957 pattern childGuard
    simpa only [d77, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2908 pattern childGuard
    simpa only [d77, d573, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2959 (pattern : Twelve) (guard : d1865 pattern = 1) : d94 pattern ≤ (0 : Int) + d594 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2958 pattern childGuard
    simpa only [d94, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2911 pattern childGuard
    simpa only [d94, d594, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2960 (pattern : Twelve) (guard : d1865 pattern = 1) : d105 pattern ≤ (0 : Int) + d609 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2959 pattern childGuard
    simpa only [d105, d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d105, d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2961 (pattern : Twelve) (guard : d1865 pattern = 1) : d111 pattern ≤ (0 : Int) + d619 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2953 pattern childGuard
    simpa only [d111, d619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2960 pattern childGuard
    simpa only [d111, d619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2962 (pattern : Twelve) (guard : d1865 pattern = 1) : d114 pattern ≤ (0 : Int) + d624 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2914 pattern childGuard
    simpa only [d114, d624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2961 pattern childGuard
    simpa only [d114, d624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2963 (pattern : Twelve) (guard : d1865 pattern = 1) : d26 pattern ≤ (0 : Int) + d513 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d26, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d26, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2837 pattern childGuard
    simpa only [d26, d513, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2964 (pattern : Twelve) (guard : d1865 pattern = 1) : d50 pattern ≤ (0 : Int) + d513 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2963 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2895 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2965 (pattern : Twelve) (guard : d1865 pattern = 1) : d72 pattern ≤ (0 : Int) + d574 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d72, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d72, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2964 pattern childGuard
    simpa only [d72, d574, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2966 (pattern : Twelve) (guard : d1865 pattern = 1) : d28 pattern ≤ (0 : Int) + d524 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d28, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d28, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2848 pattern childGuard
    simpa only [d28, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2967 (pattern : Twelve) (guard : d1865 pattern = 1) : d51 pattern ≤ (0 : Int) + d552 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2966 pattern childGuard
    simpa only [d51, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d51, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d51, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2968 (pattern : Twelve) (guard : d1865 pattern = 1) : d73 pattern ≤ (0 : Int) + d575 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d73, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d73, d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2967 pattern childGuard
    simpa only [d73, d575, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2969 (pattern : Twelve) (guard : d1865 pattern = 1) : d91 pattern ≤ (0 : Int) + d595 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2965 pattern childGuard
    simpa only [d91, d595, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d91, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2968 pattern childGuard
    simpa only [d91, d595, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2970 (pattern : Twelve) (guard : d1865 pattern = 1) : d31 pattern ≤ (0 : Int) + d525 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d31, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d31, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d31, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2971 (pattern : Twelve) (guard : d1865 pattern = 1) : d52 pattern ≤ (0 : Int) + d553 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d52, d553, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d52, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2970 pattern childGuard
    simpa only [d52, d553, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2972 (pattern : Twelve) (guard : d1865 pattern = 1) : d53 pattern ≤ (0 : Int) + d554 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d53, d554, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d53, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2877 pattern childGuard
    simpa only [d53, d554, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2973 (pattern : Twelve) (guard : d1865 pattern = 1) : d74 pattern ≤ (0 : Int) + d576 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2971 pattern childGuard
    simpa only [d74, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d74, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2972 pattern childGuard
    simpa only [d74, d576, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2974 (pattern : Twelve) (guard : d1865 pattern = 1) : d54 pattern ≤ (0 : Int) + d555 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d54, d555, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d54, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2881 pattern childGuard
    simpa only [d54, d555, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2975 (pattern : Twelve) (guard : d1865 pattern = 1) : d75 pattern ≤ (0 : Int) + d577 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2974 pattern childGuard
    simpa only [d75, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d75, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d75, d577, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2976 (pattern : Twelve) (guard : d1865 pattern = 1) : d92 pattern ≤ (0 : Int) + d596 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2973 pattern childGuard
    simpa only [d92, d596, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d92, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2975 pattern childGuard
    simpa only [d92, d596, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2977 (pattern : Twelve) (guard : d1865 pattern = 1) : d102 pattern ≤ (0 : Int) + d610 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2969 pattern childGuard
    simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2976 pattern childGuard
    simpa only [d102, d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2978 (pattern : Twelve) (guard : d1865 pattern = 1) : d76 pattern ≤ (0 : Int) + d578 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d76, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d76, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d76, d578, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2979 (pattern : Twelve) (guard : d1865 pattern = 1) : d93 pattern ≤ (0 : Int) + d597 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2965 pattern childGuard
    simpa only [d93, d597, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d93, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2978 pattern childGuard
    simpa only [d93, d597, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2980 (pattern : Twelve) (guard : d1865 pattern = 1) : d77 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2908 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2981 (pattern : Twelve) (guard : d1865 pattern = 1) : d94 pattern ≤ (0 : Int) + d598 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2980 pattern childGuard
    simpa only [d94, d598, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d94, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2911 pattern childGuard
    simpa only [d94, d598, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2982 (pattern : Twelve) (guard : d1865 pattern = 1) : d103 pattern ≤ (0 : Int) + d611 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2979 pattern childGuard
    simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2981 pattern childGuard
    simpa only [d103, d611, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2983 (pattern : Twelve) (guard : d1865 pattern = 1) : d110 pattern ≤ (0 : Int) + d620 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2977 pattern childGuard
    simpa only [d110, d620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d110, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2982 pattern childGuard
    simpa only [d110, d620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2984 (pattern : Twelve) (guard : d1865 pattern = 1) : d58 pattern ≤ (0 : Int) + d556 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d58, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d58, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2925 pattern childGuard
    simpa only [d58, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2985 (pattern : Twelve) (guard : d1865 pattern = 1) : d79 pattern ≤ (0 : Int) + d579 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d79, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d79, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2984 pattern childGuard
    simpa only [d79, d579, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2986 (pattern : Twelve) (guard : d1865 pattern = 1) : d80 pattern ≤ (0 : Int) + d580 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d80, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d80, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2885 pattern childGuard
    simpa only [d80, d580, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2987 (pattern : Twelve) (guard : d1865 pattern = 1) : d95 pattern ≤ (0 : Int) + d599 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2985 pattern childGuard
    simpa only [d95, d599, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d95, d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2986 pattern childGuard
    simpa only [d95, d599, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2988 (pattern : Twelve) (guard : d1865 pattern = 1) : d81 pattern ≤ (0 : Int) + d549 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2940 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2989 (pattern : Twelve) (guard : d1865 pattern = 1) : d96 pattern ≤ (0 : Int) + d600 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2988 pattern childGuard
    simpa only [d96, d600, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2951 pattern childGuard
    simpa only [d96, d600, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2990 (pattern : Twelve) (guard : d1865 pattern = 1) : d104 pattern ≤ (0 : Int) + d612 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2987 pattern childGuard
    simpa only [d104, d612, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2989 pattern childGuard
    simpa only [d104, d612, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2991 (pattern : Twelve) (guard : d1865 pattern = 1) : d105 pattern ≤ (0 : Int) + d613 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2981 pattern childGuard
    simpa only [d105, d613, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d105, d613, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2992 (pattern : Twelve) (guard : d1865 pattern = 1) : d111 pattern ≤ (0 : Int) + d621 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2990 pattern childGuard
    simpa only [d111, d621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2991 pattern childGuard
    simpa only [d111, d621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2993 (pattern : Twelve) (guard : d1865 pattern = 1) : d114 pattern ≤ (0 : Int) + d625 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2983 pattern childGuard
    simpa only [d114, d625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2992 pattern childGuard
    simpa only [d114, d625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2994 (pattern : Twelve) (guard : d1865 pattern = 1) : d114 pattern ≤ (0 : Int) + d627 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2962 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2993 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2995 (pattern : Twelve) (guard : d1865 pattern = 1) : d114 pattern ≤ (0 : Int) + d628 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2994 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2993 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2996 (pattern : Twelve) (guard : d1865 pattern = 1) : d120 pattern ≤ (0 : Int) + d526 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d120, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d120, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d120, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d120, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2997 (pattern : Twelve) (guard : d1865 pattern = 1) : d129 pattern ≤ (0 : Int) + d557 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d129, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2996 pattern childGuard
    simpa only [d129, d557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d129, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2854 pattern childGuard
    simpa only [d129, d557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2998 (pattern : Twelve) (guard : d1865 pattern = 1) : d136 pattern ≤ (0 : Int) + d581 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d136, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d136, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d136, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2997 pattern childGuard
    simpa only [d136, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2999 (pattern : Twelve) (guard : d1865 pattern = 1) : d144 pattern ≤ (0 : Int) + d601 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d144, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2965 pattern childGuard
    simpa only [d144, d601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d144, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2998 pattern childGuard
    simpa only [d144, d601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3000 (pattern : Twelve) (guard : d1865 pattern = 1) : d121 pattern ≤ (0 : Int) + d509 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d121, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d121, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d121, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d121, d509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3001 (pattern : Twelve) (guard : d1865 pattern = 1) : d130 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d130, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3000 pattern childGuard
    simpa only [d130, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d130, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2907 pattern childGuard
    simpa only [d130, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3002 (pattern : Twelve) (guard : d1865 pattern = 1) : d137 pattern ≤ (0 : Int) + d582 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d137, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2971 pattern childGuard
    simpa only [d137, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d137, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3001 pattern childGuard
    simpa only [d137, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3003 (pattern : Twelve) (guard : d1865 pattern = 1) : d138 pattern ≤ (0 : Int) + d583 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d138, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d138, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d138, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2997 pattern childGuard
    simpa only [d138, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3004 (pattern : Twelve) (guard : d1865 pattern = 1) : d145 pattern ≤ (0 : Int) + d602 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d145, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3002 pattern childGuard
    simpa only [d145, d602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d145, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3003 pattern childGuard
    simpa only [d145, d602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3005 (pattern : Twelve) (guard : d1865 pattern = 1) : d149 pattern ≤ (0 : Int) + d614 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d149, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2999 pattern childGuard
    simpa only [d149, d614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d149, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3004 pattern childGuard
    simpa only [d149, d614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3006 (pattern : Twelve) (guard : d1865 pattern = 1) : d139 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3001 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3007 (pattern : Twelve) (guard : d1865 pattern = 1) : d146 pattern ≤ (0 : Int) + d603 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d146, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3006 pattern childGuard
    simpa only [d146, d603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d146, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3003 pattern childGuard
    simpa only [d146, d603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3008 (pattern : Twelve) (guard : d1865 pattern = 1) : d150 pattern ≤ (0 : Int) + d615 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d150, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2999 pattern childGuard
    simpa only [d150, d615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d150, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3007 pattern childGuard
    simpa only [d150, d615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3009 (pattern : Twelve) (guard : d1865 pattern = 1) : d153 pattern ≤ (0 : Int) + d622 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d153, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3005 pattern childGuard
    simpa only [d153, d622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d153, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3008 pattern childGuard
    simpa only [d153, d622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3010 (pattern : Twelve) (guard : d1865 pattern = 1) : d122 pattern ≤ (0 : Int) + d527 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d122, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d122, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d122, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2934 pattern childGuard
    simpa only [d122, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3011 (pattern : Twelve) (guard : d1865 pattern = 1) : d131 pattern ≤ (0 : Int) + d558 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d131, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3000 pattern childGuard
    simpa only [d131, d558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d131, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3010 pattern childGuard
    simpa only [d131, d558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3012 (pattern : Twelve) (guard : d1865 pattern = 1) : d140 pattern ≤ (0 : Int) + d584 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d140, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d140, d584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d140, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3011 pattern childGuard
    simpa only [d140, d584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3013 (pattern : Twelve) (guard : d1865 pattern = 1) : d123 pattern ≤ (0 : Int) + d518 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d123, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2843 pattern childGuard
    simpa only [d123, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d123, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2924 pattern childGuard
    simpa only [d123, d518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3014 (pattern : Twelve) (guard : d1865 pattern = 1) : d132 pattern ≤ (0 : Int) + d556 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d132, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2906 pattern childGuard
    simpa only [d132, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d132, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3013 pattern childGuard
    simpa only [d132, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3015 (pattern : Twelve) (guard : d1865 pattern = 1) : d141 pattern ≤ (0 : Int) + d585 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d141, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3014 pattern childGuard
    simpa only [d141, d585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d141, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2997 pattern childGuard
    simpa only [d141, d585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3016 (pattern : Twelve) (guard : d1865 pattern = 1) : d147 pattern ≤ (0 : Int) + d604 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d147, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3012 pattern childGuard
    simpa only [d147, d604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d147, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3015 pattern childGuard
    simpa only [d147, d604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3017 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (0 : Int) + d5 pattern := by
  omega
theorem c3018 (pattern : Twelve) (guard : d1865 pattern = 1) : d118 pattern ≤ (0 : Int) + d497 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d118, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1865, d118, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d118, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1865, d118, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3019 (pattern : Twelve) (guard : d1865 pattern = 1) : d124 pattern ≤ (0 : Int) + d528 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d124, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d124, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d124, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3018 pattern childGuard
    simpa only [d124, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3020 (pattern : Twelve) (guard : d0 pattern = 1) : d117 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3021 (pattern : Twelve) (guard : d1865 pattern = 1) : d119 pattern ≤ (0 : Int) + d492 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d119, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1865, d119, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d119, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3020 pattern childGuard
    simpa only [d1865, d119, d492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3022 (pattern : Twelve) (guard : d1865 pattern = 1) : d125 pattern ≤ (0 : Int) + d529 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d125, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3021 pattern childGuard
    simpa only [d125, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d125, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d125, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3023 (pattern : Twelve) (guard : d1865 pattern = 1) : d133 pattern ≤ (0 : Int) + d559 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d133, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3019 pattern childGuard
    simpa only [d133, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d133, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3022 pattern childGuard
    simpa only [d133, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3024 (pattern : Twelve) (guard : d1865 pattern = 1) : d142 pattern ≤ (0 : Int) + d586 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d142, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d142, d586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d142, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3023 pattern childGuard
    simpa only [d142, d586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3025 (pattern : Twelve) (guard : d0 pattern = 1) : d5 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3026 (pattern : Twelve) (guard : d1865 pattern = 1) : d5 pattern ≤ (0 : Int) + d497 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3025 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3027 (pattern : Twelve) (guard : d1865 pattern = 1) : d126 pattern ≤ (0 : Int) + d528 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d126, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2870 pattern childGuard
    simpa only [d126, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d126, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3026 pattern childGuard
    simpa only [d126, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3028 (pattern : Twelve) (guard : d1865 pattern = 1) : d47 pattern ≤ (0 : Int) + d529 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d47, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2924 pattern childGuard
    simpa only [d47, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d47, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d47, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3029 (pattern : Twelve) (guard : d1865 pattern = 1) : d134 pattern ≤ (0 : Int) + d559 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d134, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3027 pattern childGuard
    simpa only [d134, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d134, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3028 pattern childGuard
    simpa only [d134, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3030 (pattern : Twelve) (guard : d1865 pattern = 1) : d127 pattern ≤ (0 : Int) + d530 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d127, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2883 pattern childGuard
    simpa only [d127, d530, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d127, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d127, d530, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3031 (pattern : Twelve) (guard : d1865 pattern = 1) : d128 pattern ≤ (0 : Int) + d531 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d128, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2867 pattern childGuard
    simpa only [d128, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d128, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d128, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3032 (pattern : Twelve) (guard : d1865 pattern = 1) : d135 pattern ≤ (0 : Int) + d560 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d135, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3030 pattern childGuard
    simpa only [d135, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d135, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3031 pattern childGuard
    simpa only [d135, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3033 (pattern : Twelve) (guard : d1865 pattern = 1) : d143 pattern ≤ (0 : Int) + d587 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d143, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3029 pattern childGuard
    simpa only [d143, d587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d143, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3032 pattern childGuard
    simpa only [d143, d587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3034 (pattern : Twelve) (guard : d1865 pattern = 1) : d148 pattern ≤ (0 : Int) + d605 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d148, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3024 pattern childGuard
    simpa only [d148, d605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d148, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3033 pattern childGuard
    simpa only [d148, d605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3035 (pattern : Twelve) (guard : d1865 pattern = 1) : d151 pattern ≤ (0 : Int) + d616 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d151, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3016 pattern childGuard
    simpa only [d151, d616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d151, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3034 pattern childGuard
    simpa only [d151, d616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3036 (pattern : Twelve) (guard : d1865 pattern = 1) : d152 pattern ≤ (0 : Int) + d617 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d152, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3007 pattern childGuard
    simpa only [d152, d617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d152, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d152, d617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3037 (pattern : Twelve) (guard : d1865 pattern = 1) : d154 pattern ≤ (0 : Int) + d623 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d154, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3035 pattern childGuard
    simpa only [d154, d623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d154, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3036 pattern childGuard
    simpa only [d154, d623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3038 (pattern : Twelve) (guard : d1865 pattern = 1) : d155 pattern ≤ (0 : Int) + d626 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d155, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3009 pattern childGuard
    simpa only [d155, d626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d155, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3037 pattern childGuard
    simpa only [d155, d626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3039 (pattern : Twelve) (guard : d1865 pattern = 1) : d156 pattern ≤ (0 : Int) + d629 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d156, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2995 pattern childGuard
    simpa only [d156, d629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d156, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3038 pattern childGuard
    simpa only [d156, d629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3040 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d7 pattern := by
  omega
theorem c3041 (pattern : Twelve) (guard : d1865 pattern = 1) : d814 pattern ≤ (0 : Int) + d1105 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d814, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3040 pattern childGuard
    simpa only [d1865, d814, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d814, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1865, d814, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3042 (pattern : Twelve) (guard : d1865 pattern = 1) : d816 pattern ≤ (0 : Int) + d1108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d816, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d816, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d816, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2837 pattern childGuard
    simpa only [d816, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3043 (pattern : Twelve) (guard : d1865 pattern = 1) : d824 pattern ≤ (0 : Int) + d1118 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2838 pattern childGuard
    simpa only [d824, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3042 pattern childGuard
    simpa only [d824, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3044 (pattern : Twelve) (guard : d1865 pattern = 1) : d838 pattern ≤ (0 : Int) + d1132 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2845 pattern childGuard
    simpa only [d838, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3043 pattern childGuard
    simpa only [d838, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3045 (pattern : Twelve) (guard : d1865 pattern = 1) : d17 pattern ≤ (0 : Int) + d501 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2836 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3046 (pattern : Twelve) (guard : d1865 pattern = 1) : d17 pattern ≤ (0 : Int) + d1119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3045 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3047 (pattern : Twelve) (guard : d1865 pattern = 1) : d817 pattern ≤ (0 : Int) + d1109 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d817, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2852 pattern childGuard
    simpa only [d817, d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d817, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d817, d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3048 (pattern : Twelve) (guard : d1865 pattern = 1) : d825 pattern ≤ (0 : Int) + d1120 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d825, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d825, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d825, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2949 pattern childGuard
    simpa only [d825, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3049 (pattern : Twelve) (guard : d1865 pattern = 1) : d839 pattern ≤ (0 : Int) + d1133 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3046 pattern childGuard
    simpa only [d839, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3048 pattern childGuard
    simpa only [d839, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3050 (pattern : Twelve) (guard : d1865 pattern = 1) : d853 pattern ≤ (0 : Int) + d1152 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3044 pattern childGuard
    simpa only [d853, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3049 pattern childGuard
    simpa only [d853, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3051 (pattern : Twelve) (guard : d1865 pattern = 1) : d56 pattern ≤ (0 : Int) + d1121 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2871 pattern childGuard
    simpa only [d56, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d56, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2904 pattern childGuard
    simpa only [d56, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3052 (pattern : Twelve) (guard : d1865 pattern = 1) : d818 pattern ≤ (0 : Int) + d1110 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d818, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d818, d1110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d818, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d818, d1110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3053 (pattern : Twelve) (guard : d1865 pattern = 1) : d826 pattern ≤ (0 : Int) + d1122 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d826, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d826, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d826, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3052 pattern childGuard
    simpa only [d826, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3054 (pattern : Twelve) (guard : d1865 pattern = 1) : d840 pattern ≤ (0 : Int) + d1134 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3051 pattern childGuard
    simpa only [d840, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3053 pattern childGuard
    simpa only [d840, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3055 (pattern : Twelve) (guard : d1865 pattern = 1) : d827 pattern ≤ (0 : Int) + d544 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d827, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d827, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d827, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2907 pattern childGuard
    simpa only [d827, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3056 (pattern : Twelve) (guard : d1865 pattern = 1) : d841 pattern ≤ (0 : Int) + d1135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d841, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3055 pattern childGuard
    simpa only [d841, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d841, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3048 pattern childGuard
    simpa only [d841, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3057 (pattern : Twelve) (guard : d1865 pattern = 1) : d854 pattern ≤ (0 : Int) + d1153 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3054 pattern childGuard
    simpa only [d854, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3056 pattern childGuard
    simpa only [d854, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3058 (pattern : Twelve) (guard : d1865 pattern = 1) : d861 pattern ≤ (0 : Int) + d1164 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3050 pattern childGuard
    simpa only [d861, d1164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3057 pattern childGuard
    simpa only [d861, d1164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3059 (pattern : Twelve) (guard : d1865 pattern = 1) : d824 pattern ≤ (0 : Int) + d1123 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2895 pattern childGuard
    simpa only [d824, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3042 pattern childGuard
    simpa only [d824, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3060 (pattern : Twelve) (guard : d1865 pattern = 1) : d838 pattern ≤ (0 : Int) + d1136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2898 pattern childGuard
    simpa only [d838, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3059 pattern childGuard
    simpa only [d838, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3061 (pattern : Twelve) (guard : d1865 pattern = 1) : d839 pattern ≤ (0 : Int) + d1137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2873 pattern childGuard
    simpa only [d839, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3048 pattern childGuard
    simpa only [d839, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3062 (pattern : Twelve) (guard : d1865 pattern = 1) : d853 pattern ≤ (0 : Int) + d1154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3060 pattern childGuard
    simpa only [d853, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3061 pattern childGuard
    simpa only [d853, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3063 (pattern : Twelve) (guard : d1865 pattern = 1) : d840 pattern ≤ (0 : Int) + d1138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2910 pattern childGuard
    simpa only [d840, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3053 pattern childGuard
    simpa only [d840, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3064 (pattern : Twelve) (guard : d1865 pattern = 1) : d854 pattern ≤ (0 : Int) + d1155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3063 pattern childGuard
    simpa only [d854, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3056 pattern childGuard
    simpa only [d854, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3065 (pattern : Twelve) (guard : d1865 pattern = 1) : d861 pattern ≤ (0 : Int) + d1165 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3062 pattern childGuard
    simpa only [d861, d1165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3064 pattern childGuard
    simpa only [d861, d1165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3066 (pattern : Twelve) (guard : d1865 pattern = 1) : d861 pattern ≤ (0 : Int) + d1173 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3058 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3065 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3067 (pattern : Twelve) (guard : d1865 pattern = 1) : d819 pattern ≤ (0 : Int) + d1111 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d819, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d819, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d819, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2924 pattern childGuard
    simpa only [d819, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3068 (pattern : Twelve) (guard : d1865 pattern = 1) : d828 pattern ≤ (0 : Int) + d1124 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d828, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d828, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d828, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3067 pattern childGuard
    simpa only [d828, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3069 (pattern : Twelve) (guard : d1865 pattern = 1) : d842 pattern ≤ (0 : Int) + d1139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2928 pattern childGuard
    simpa only [d842, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3068 pattern childGuard
    simpa only [d842, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3070 (pattern : Twelve) (guard : d1865 pattern = 1) : d843 pattern ≤ (0 : Int) + d1140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d843, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2884 pattern childGuard
    simpa only [d843, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d843, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3048 pattern childGuard
    simpa only [d843, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3071 (pattern : Twelve) (guard : d1865 pattern = 1) : d855 pattern ≤ (0 : Int) + d1156 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3069 pattern childGuard
    simpa only [d855, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3070 pattern childGuard
    simpa only [d855, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3072 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  omega
theorem c3073 (pattern : Twelve) (guard : d1865 pattern = 1) : d815 pattern ≤ (0 : Int) + d1106 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d815, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3072 pattern childGuard
    simpa only [d1865, d815, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d815, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2923 pattern childGuard
    simpa only [d1865, d815, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3074 (pattern : Twelve) (guard : d1865 pattern = 1) : d820 pattern ≤ (0 : Int) + d1112 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d820, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3073 pattern childGuard
    simpa only [d820, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d820, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d820, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3075 (pattern : Twelve) (guard : d1865 pattern = 1) : d829 pattern ≤ (0 : Int) + d1125 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d829, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2945 pattern childGuard
    simpa only [d829, d1125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d829, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3074 pattern childGuard
    simpa only [d829, d1125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3076 (pattern : Twelve) (guard : d1865 pattern = 1) : d844 pattern ≤ (0 : Int) + d1141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2942 pattern childGuard
    simpa only [d844, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3075 pattern childGuard
    simpa only [d844, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3077 (pattern : Twelve) (guard : d1865 pattern = 1) : d830 pattern ≤ (0 : Int) + d549 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d830, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2945 pattern childGuard
    simpa only [d830, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d830, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2939 pattern childGuard
    simpa only [d830, d549, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3078 (pattern : Twelve) (guard : d1865 pattern = 1) : d821 pattern ≤ (0 : Int) + d1113 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d821, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2948 pattern childGuard
    simpa only [d821, d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d821, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d821, d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3079 (pattern : Twelve) (guard : d1865 pattern = 1) : d822 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2876 pattern childGuard
    simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
