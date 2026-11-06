/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons070
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9940 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (8 : Int) + d833 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9939 pattern childGuard
    simpa only [d66, d833, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9941 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (8 : Int) + d848 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9940 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9932 pattern childGuard
    simpa only [d86, d848, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9942 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (8 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9938 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9941 pattern childGuard
    simpa only [d99, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9943 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (8 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9925 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9942 pattern childGuard
    simpa only [d107, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9944 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (8 : Int) + d864 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9935 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9943 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9945 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (8 : Int) + d46 pattern := by
  omega
theorem c9946 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (8 : Int) + d834 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9945 pattern childGuard
    simpa only [d67, d834, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9947 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (8 : Int) + d849 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9849 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9946 pattern childGuard
    simpa only [d87, d849, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9948 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (8 : Int) + d38 pattern := by
  omega
theorem c9949 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (8 : Int) + d835 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9948 pattern childGuard
    simpa only [d68, d835, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9950 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (8 : Int) + d850 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9949 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9932 pattern childGuard
    simpa only [d88, d850, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9951 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (8 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9947 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9950 pattern childGuard
    simpa only [d100, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9952 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (8 : Int) + d47 pattern := by
  omega
theorem c9953 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (8 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9900 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9952 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9954 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (8 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9895 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9953 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9955 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (8 : Int) + d48 pattern := by
  omega
theorem c9956 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (8 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9900 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9955 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9957 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (8 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9910 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d49, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9958 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (8 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9911 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9957 pattern childGuard
    simpa only [d71, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9959 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (8 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9956 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9958 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9960 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (8 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9954 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9959 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9961 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (8 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9951 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9960 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9962 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (8 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9942 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9963 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (8 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9961 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9962 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9964 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (8 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9944 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9963 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9965 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (8 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9922 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9964 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9966 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (8 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9818 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9833 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9967 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (8 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9819 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9966 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9968 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9833 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9969 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9968 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9970 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (8 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9967 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9969 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9971 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (8 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9823 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9968 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9972 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (8 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9971 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9969 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9973 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (8 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9970 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9972 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9974 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (8 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9820 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9973 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9975 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d6 pattern := by
  change (0 : Int) ≤ (8 : Int) + 6
  decide
theorem c9976 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d6 pattern := by
  change (2 : Int) ≤ (8 : Int) + 6
  decide
theorem c9977 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9975 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9976 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9978 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d6 pattern := by
  change (1 : Int) ≤ (8 : Int) + 6
  decide
theorem c9979 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9978 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9850 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9980 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9977 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9979 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9981 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9976 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9853 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9982 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9981 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9852 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9983 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9980 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9982 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9984 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9982 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9985 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9983 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9984 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9986 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (8 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9987 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (8 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9974 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9986 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9988 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d4 pattern := by
  change (3 : Int) ≤ (8 : Int) + 4
  decide
theorem c9989 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (8 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9836 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9988 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9990 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (8 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9859 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9989 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9991 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (8 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9967 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9990 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9992 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (8 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9971 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9993 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (8 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9991 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9992 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9994 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (8 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9884 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9993 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9995 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (8 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9996 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (8 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9995 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9997 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (8 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9996 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9998 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (8 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9994 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9997 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9999 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (8 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9987 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9998 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10000 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9889 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9988 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10001 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9889 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10000 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10002 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (8 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9971 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10001 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10003 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (8 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9991 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10002 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10004 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (8 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10003 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10005 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (8 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10006 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (8 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10004 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10005 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10007 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (8 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9898 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9909 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10008 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (8 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9990 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10007 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10009 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (8 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9901 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10000 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10010 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (8 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10009 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10011 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (8 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10008 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10010 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10012 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (8 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9907 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10011 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10013 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (8 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9911 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9931 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10014 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9982 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9863 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10015 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9863 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10016 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (8 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10014 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10015 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10017 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (8 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10013 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10016 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10018 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (8 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10012 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10017 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10019 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (8 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10006 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10018 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10020 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (8 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9998 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10021 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (8 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10019 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10020 pattern childGuard
    simpa only [d867, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10022 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (8 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9999 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10021 pattern childGuard
    simpa only [d869, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10023 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (8 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9860 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10024 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (8 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10023 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10025 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (8 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9974 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10024 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10026 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (8 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9969 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d45, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10027 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (8 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9991 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10026 pattern childGuard
    simpa only [d832, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10028 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (8 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9884 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10027 pattern childGuard
    simpa only [d847, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10029 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (8 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9906 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10030 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (8 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10029 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10031 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (8 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10028 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10030 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10032 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (8 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10025 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10031 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10033 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (8 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9969 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10001 pattern childGuard
    simpa only [d46, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10034 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (8 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9991 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10033 pattern childGuard
    simpa only [d834, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10035 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (8 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9861 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10034 pattern childGuard
    simpa only [d849, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10036 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (8 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9900 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10037 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (8 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10036 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9985 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10038 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (8 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10035 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10037 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10039 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (8 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10001 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10040 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (8 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10008 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10039 pattern childGuard
    simpa only [d836, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10041 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (8 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9907 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10040 pattern childGuard
    simpa only [d851, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10042 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (8 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9899 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10043 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (8 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9911 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10042 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10044 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (8 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10043 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10016 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10045 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (8 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10041 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10044 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10046 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (8 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10038 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10045 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10047 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (8 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10031 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10048 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (8 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10046 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10047 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10049 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (8 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10032 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10048 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10050 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (8 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10022 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10049 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10051 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (8 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9831 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9835 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10052 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9821 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9830 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10053 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (8 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10052 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9835 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10054 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (8 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10051 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10053 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10055 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (8 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10054 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10053 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10056 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (8 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9832 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10055 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10057 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (8 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9843 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10058 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (8 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10056 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10057 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10059 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (8 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9988 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9853 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10060 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (8 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9838 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10059 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10061 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (8 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10051 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10060 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10062 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (8 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10053 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10063 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (8 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10061 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10062 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10064 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (8 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9996 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10063 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10065 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (8 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9843 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9914 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10066 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (8 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10065 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9845 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10067 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (8 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10066 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10068 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (8 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10064 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10067 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10069 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (8 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10058 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10068 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10070 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9889 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9837 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10071 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (8 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10070 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10059 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10072 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (8 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10053 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10071 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10073 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (8 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10061 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10072 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10074 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (8 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9872 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10073 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10075 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (8 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10065 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10076 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (8 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10074 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10075 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10077 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (8 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9909 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9862 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10078 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (8 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10060 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10077 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10079 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (8 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10071 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9844 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
