/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons117
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c16520 (pattern : Twelve) (guard : d2746 pattern = 1) : d893 pattern ≤ (1 : Int) + d2954 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d893, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16484 pattern childGuard
    simpa only [d893, d2954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d893, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16514 pattern childGuard
    simpa only [d893, d2954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16521 (pattern : Twelve) (guard : d2746 pattern = 1) : d899 pattern ≤ (1 : Int) + d2955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d899, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16519 pattern childGuard
    simpa only [d899, d2955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d899, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16520 pattern childGuard
    simpa only [d899, d2955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16522 (pattern : Twelve) (guard : d2746 pattern = 1) : d902 pattern ≤ (1 : Int) + d2956 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d902, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16516 pattern childGuard
    simpa only [d902, d2956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d902, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16521 pattern childGuard
    simpa only [d902, d2956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16523 (pattern : Twelve) (guard : d2746 pattern = 1) : d878 pattern ≤ (1 : Int) + d2957 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d878, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16473 pattern childGuard
    simpa only [d878, d2957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d878, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16420 pattern childGuard
    simpa only [d878, d2957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16524 (pattern : Twelve) (guard : d2746 pattern = 1) : d885 pattern ≤ (1 : Int) + d2958 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d885, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16517 pattern childGuard
    simpa only [d885, d2958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d885, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16523 pattern childGuard
    simpa only [d885, d2958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16525 (pattern : Twelve) (guard : d2746 pattern = 1) : d894 pattern ≤ (1 : Int) + d2959 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d894, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16378 pattern childGuard
    simpa only [d894, d2959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d894, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16524 pattern childGuard
    simpa only [d894, d2959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16526 (pattern : Twelve) (guard : d2746 pattern = 1) : d879 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16458 pattern childGuard
    simpa only [d879, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16527 (pattern : Twelve) (guard : d2746 pattern = 1) : d886 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16526 pattern childGuard
    simpa only [d886, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16528 (pattern : Twelve) (guard : d2746 pattern = 1) : d895 pattern ≤ (1 : Int) + d2960 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d895, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16527 pattern childGuard
    simpa only [d895, d2960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d895, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16514 pattern childGuard
    simpa only [d895, d2960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16529 (pattern : Twelve) (guard : d2746 pattern = 1) : d900 pattern ≤ (1 : Int) + d2961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d900, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16525 pattern childGuard
    simpa only [d900, d2961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d900, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16528 pattern childGuard
    simpa only [d900, d2961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16530 (pattern : Twelve) (guard : d2746 pattern = 1) : d873 pattern ≤ (1 : Int) + d4 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16226 pattern childGuard
    simpa only [d2746, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16419 pattern childGuard
    simpa only [d2746, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16531 (pattern : Twelve) (guard : d2746 pattern = 1) : d880 pattern ≤ (1 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d880, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16530 pattern childGuard
    simpa only [d880, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d880, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d880, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16532 (pattern : Twelve) (guard : d2746 pattern = 1) : d887 pattern ≤ (1 : Int) + d2925 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d887, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16463 pattern childGuard
    simpa only [d887, d2925, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d887, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16531 pattern childGuard
    simpa only [d887, d2925, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16533 (pattern : Twelve) (guard : d2746 pattern = 1) : d896 pattern ≤ (1 : Int) + d2962 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d896, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16414 pattern childGuard
    simpa only [d896, d2962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d896, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16532 pattern childGuard
    simpa only [d896, d2962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16534 (pattern : Twelve) (guard : d2746 pattern = 1) : d881 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16392 pattern childGuard
    simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16455 pattern childGuard
    simpa only [d881, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16535 (pattern : Twelve) (guard : d2746 pattern = 1) : d888 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16534 pattern childGuard
    simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16459 pattern childGuard
    simpa only [d888, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16536 (pattern : Twelve) (guard : d2746 pattern = 1) : d889 pattern ≤ (1 : Int) + d2963 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d889, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16425 pattern childGuard
    simpa only [d889, d2963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d889, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d889, d2963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16537 (pattern : Twelve) (guard : d2746 pattern = 1) : d897 pattern ≤ (1 : Int) + d2964 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d897, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16535 pattern childGuard
    simpa only [d897, d2964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d897, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16536 pattern childGuard
    simpa only [d897, d2964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16538 (pattern : Twelve) (guard : d2746 pattern = 1) : d901 pattern ≤ (1 : Int) + d2965 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d901, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16533 pattern childGuard
    simpa only [d901, d2965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d901, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16537 pattern childGuard
    simpa only [d901, d2965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16539 (pattern : Twelve) (guard : d2746 pattern = 1) : d903 pattern ≤ (1 : Int) + d2966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d903, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16529 pattern childGuard
    simpa only [d903, d2966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d903, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16538 pattern childGuard
    simpa only [d903, d2966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16540 (pattern : Twelve) (guard : d2746 pattern = 1) : d904 pattern ≤ (1 : Int) + d2967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d904, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16521 pattern childGuard
    simpa only [d904, d2967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d904, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d904, d2967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16541 (pattern : Twelve) (guard : d2746 pattern = 1) : d905 pattern ≤ (1 : Int) + d2968 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d905, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16539 pattern childGuard
    simpa only [d905, d2968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d905, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16540 pattern childGuard
    simpa only [d905, d2968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16542 (pattern : Twelve) (guard : d2746 pattern = 1) : d906 pattern ≤ (1 : Int) + d2969 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d906, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16522 pattern childGuard
    simpa only [d906, d2969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d906, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16541 pattern childGuard
    simpa only [d906, d2969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16543 (pattern : Twelve) (guard : d2746 pattern = 1) : d907 pattern ≤ (1 : Int) + d2970 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d907, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16506 pattern childGuard
    simpa only [d907, d2970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d907, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16542 pattern childGuard
    simpa only [d907, d2970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16544 (pattern : Twelve) (guard : d2746 pattern = 1) : d1275 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16138 pattern childGuard
    simpa only [d2746, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16507 pattern childGuard
    simpa only [d2746, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16545 (pattern : Twelve) (guard : d2746 pattern = 1) : d1278 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16544 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16546 (pattern : Twelve) (guard : d2746 pattern = 1) : d1284 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16545 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16547 (pattern : Twelve) (guard : d2746 pattern = 1) : d1293 pattern ≤ (1 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1293, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d1293, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1293, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16546 pattern childGuard
    simpa only [d1293, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16548 (pattern : Twelve) (guard : d2746 pattern = 1) : d1294 pattern ≤ (1 : Int) + d2971 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1294, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d1294, d2971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1294, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1294, d2971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16549 (pattern : Twelve) (guard : d2746 pattern = 1) : d1305 pattern ≤ (1 : Int) + d2972 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1305, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16547 pattern childGuard
    simpa only [d1305, d2972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1305, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16548 pattern childGuard
    simpa only [d1305, d2972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16550 (pattern : Twelve) (guard : d2746 pattern = 1) : d1276 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16178 pattern childGuard
    simpa only [d2746, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16457 pattern childGuard
    simpa only [d2746, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16551 (pattern : Twelve) (guard : d2746 pattern = 1) : d1279 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1279, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16544 pattern childGuard
    simpa only [d1279, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1279, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16550 pattern childGuard
    simpa only [d1279, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16552 (pattern : Twelve) (guard : d2746 pattern = 1) : d1280 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1280, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16553 (pattern : Twelve) (guard : d2746 pattern = 1) : d1285 pattern ≤ (1 : Int) + d2973 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1285, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16551 pattern childGuard
    simpa only [d1285, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1285, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16552 pattern childGuard
    simpa only [d1285, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16554 (pattern : Twelve) (guard : d2746 pattern = 1) : d1295 pattern ≤ (1 : Int) + d2974 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1295, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16484 pattern childGuard
    simpa only [d1295, d2974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1295, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16553 pattern childGuard
    simpa only [d1295, d2974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16555 (pattern : Twelve) (guard : d2746 pattern = 1) : d1286 pattern ≤ (1 : Int) + d2973 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1286, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d1286, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1286, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16374 pattern childGuard
    simpa only [d1286, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16556 (pattern : Twelve) (guard : d2746 pattern = 1) : d1296 pattern ≤ (1 : Int) + d2975 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1296, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16555 pattern childGuard
    simpa only [d1296, d2975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1296, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1296, d2975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16557 (pattern : Twelve) (guard : d2746 pattern = 1) : d1306 pattern ≤ (1 : Int) + d2976 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1306, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16554 pattern childGuard
    simpa only [d1306, d2976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1306, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16556 pattern childGuard
    simpa only [d1306, d2976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16558 (pattern : Twelve) (guard : d2746 pattern = 1) : d1313 pattern ≤ (1 : Int) + d2977 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1313, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16549 pattern childGuard
    simpa only [d1313, d2977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1313, d2977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16557 pattern childGuard
    simpa only [d1313, d2977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16559 (pattern : Twelve) (guard : d2746 pattern = 1) : d1281 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16458 pattern childGuard
    simpa only [d1281, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16560 (pattern : Twelve) (guard : d2746 pattern = 1) : d1287 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16551 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16559 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16561 (pattern : Twelve) (guard : d2746 pattern = 1) : d1297 pattern ≤ (1 : Int) + d2978 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1297, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d1297, d2978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1297, d2978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16560 pattern childGuard
    simpa only [d1297, d2978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16562 (pattern : Twelve) (guard : d2746 pattern = 1) : d1298 pattern ≤ (1 : Int) + d2979 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1298, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d1298, d2979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1298, d2979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1298, d2979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16563 (pattern : Twelve) (guard : d2746 pattern = 1) : d1307 pattern ≤ (1 : Int) + d2980 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1307, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16561 pattern childGuard
    simpa only [d1307, d2980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1307, d2980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16562 pattern childGuard
    simpa only [d1307, d2980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16564 (pattern : Twelve) (guard : d2746 pattern = 1) : d1277 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16267 pattern childGuard
    simpa only [d2746, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16385 pattern childGuard
    simpa only [d2746, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16565 (pattern : Twelve) (guard : d2746 pattern = 1) : d1282 pattern ≤ (1 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1282, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16550 pattern childGuard
    simpa only [d1282, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1282, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16564 pattern childGuard
    simpa only [d1282, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16566 (pattern : Twelve) (guard : d2746 pattern = 1) : d1288 pattern ≤ (1 : Int) + d2981 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1288, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16565 pattern childGuard
    simpa only [d1288, d2981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1288, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16459 pattern childGuard
    simpa only [d1288, d2981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16567 (pattern : Twelve) (guard : d2746 pattern = 1) : d1299 pattern ≤ (1 : Int) + d2982 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1299, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16497 pattern childGuard
    simpa only [d1299, d2982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1299, d2982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16566 pattern childGuard
    simpa only [d1299, d2982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16568 (pattern : Twelve) (guard : d2746 pattern = 1) : d1289 pattern ≤ (1 : Int) + d2981 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1289, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16498 pattern childGuard
    simpa only [d1289, d2981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1289, d2981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16425 pattern childGuard
    simpa only [d1289, d2981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16569 (pattern : Twelve) (guard : d2746 pattern = 1) : d1300 pattern ≤ (1 : Int) + d2983 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1300, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16568 pattern childGuard
    simpa only [d1300, d2983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1300, d2983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1300, d2983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16570 (pattern : Twelve) (guard : d2746 pattern = 1) : d1308 pattern ≤ (1 : Int) + d2984 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1308, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16567 pattern childGuard
    simpa only [d1308, d2984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1308, d2984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16569 pattern childGuard
    simpa only [d1308, d2984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16571 (pattern : Twelve) (guard : d2746 pattern = 1) : d1314 pattern ≤ (1 : Int) + d2985 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1314, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16563 pattern childGuard
    simpa only [d1314, d2985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1314, d2985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16570 pattern childGuard
    simpa only [d1314, d2985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16572 (pattern : Twelve) (guard : d2746 pattern = 1) : d1315 pattern ≤ (1 : Int) + d2986 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1315, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16557 pattern childGuard
    simpa only [d1315, d2986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1315, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1315, d2986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16573 (pattern : Twelve) (guard : d2746 pattern = 1) : d1319 pattern ≤ (1 : Int) + d2987 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1319, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16571 pattern childGuard
    simpa only [d1319, d2987, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1319, d2987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16572 pattern childGuard
    simpa only [d1319, d2987, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16574 (pattern : Twelve) (guard : d2746 pattern = 1) : d1321 pattern ≤ (1 : Int) + d2988 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1321, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16558 pattern childGuard
    simpa only [d1321, d2988, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1321, d2988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16573 pattern childGuard
    simpa only [d1321, d2988, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16575 (pattern : Twelve) (guard : d7 pattern = 1) : d11 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15953 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11183 pattern childGuard
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16576 (pattern : Twelve) (guard : d0 pattern = 1) : d16 pattern ≤ (1 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16577 (pattern : Twelve) (guard : d2746 pattern = 1) : d1324 pattern ≤ (1 : Int) + d2 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d7 pattern = 1 := by simpa only [d2746, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16575 pattern childGuard
    simpa only [d2746, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2746, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16576 pattern childGuard
    simpa only [d2746, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16578 (pattern : Twelve) (guard : d2746 pattern = 1) : d1325 pattern ≤ (1 : Int) + d2989 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1325, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16544 pattern childGuard
    simpa only [d1325, d2989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1325, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1325, d2989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16579 (pattern : Twelve) (guard : d2746 pattern = 1) : d1326 pattern ≤ (1 : Int) + d2989 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1326, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1326, d2989, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1326, d2989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1326, d2989, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16580 (pattern : Twelve) (guard : d2746 pattern = 1) : d1333 pattern ≤ (1 : Int) + d2989 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16578 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16579 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16581 (pattern : Twelve) (guard : d2746 pattern = 1) : d1339 pattern ≤ (1 : Int) + d2990 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1339, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16363 pattern childGuard
    simpa only [d1339, d2990, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1339, d2990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16580 pattern childGuard
    simpa only [d1339, d2990, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16582 (pattern : Twelve) (guard : d2746 pattern = 1) : d1345 pattern ≤ (1 : Int) + d2991 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1345, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16581 pattern childGuard
    simpa only [d1345, d2991, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1345, d2991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16548 pattern childGuard
    simpa only [d1345, d2991, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16583 (pattern : Twelve) (guard : d2746 pattern = 1) : d1327 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1327, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16544 pattern childGuard
    simpa only [d1327, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1327, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16458 pattern childGuard
    simpa only [d1327, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16584 (pattern : Twelve) (guard : d2746 pattern = 1) : d1334 pattern ≤ (1 : Int) + d2973 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1334, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16583 pattern childGuard
    simpa only [d1334, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1334, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16552 pattern childGuard
    simpa only [d1334, d2973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16585 (pattern : Twelve) (guard : d2746 pattern = 1) : d1340 pattern ≤ (1 : Int) + d2974 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1340, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16484 pattern childGuard
    simpa only [d1340, d2974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1340, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16584 pattern childGuard
    simpa only [d1340, d2974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16586 (pattern : Twelve) (guard : d2746 pattern = 1) : d1346 pattern ≤ (1 : Int) + d2976 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1346, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16585 pattern childGuard
    simpa only [d1346, d2976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1346, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16556 pattern childGuard
    simpa only [d1346, d2976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16587 (pattern : Twelve) (guard : d2746 pattern = 1) : d1349 pattern ≤ (1 : Int) + d2992 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1349, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16582 pattern childGuard
    simpa only [d1349, d2992, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1349, d2992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16586 pattern childGuard
    simpa only [d1349, d2992, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16588 (pattern : Twelve) (guard : d2746 pattern = 1) : d1328 pattern ≤ (1 : Int) + d2950 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1328, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16508 pattern childGuard
    simpa only [d1328, d2950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1328, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16564 pattern childGuard
    simpa only [d1328, d2950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16589 (pattern : Twelve) (guard : d2746 pattern = 1) : d1335 pattern ≤ (1 : Int) + d2993 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1335, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16583 pattern childGuard
    simpa only [d1335, d2993, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1335, d2993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16588 pattern childGuard
    simpa only [d1335, d2993, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16590 (pattern : Twelve) (guard : d2746 pattern = 1) : d1341 pattern ≤ (1 : Int) + d2994 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1341, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16393 pattern childGuard
    simpa only [d1341, d2994, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1341, d2994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16589 pattern childGuard
    simpa only [d1341, d2994, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16591 (pattern : Twelve) (guard : d2746 pattern = 1) : d1329 pattern ≤ (1 : Int) + d2957 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1329, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d1329, d2957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1329, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16381 pattern childGuard
    simpa only [d1329, d2957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16592 (pattern : Twelve) (guard : d2746 pattern = 1) : d1336 pattern ≤ (1 : Int) + d2995 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1336, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d1336, d2995, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1336, d2995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16591 pattern childGuard
    simpa only [d1336, d2995, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16593 (pattern : Twelve) (guard : d2746 pattern = 1) : d1342 pattern ≤ (1 : Int) + d2996 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1342, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16592 pattern childGuard
    simpa only [d1342, d2996, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1342, d2996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1342, d2996, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16594 (pattern : Twelve) (guard : d2746 pattern = 1) : d1347 pattern ≤ (1 : Int) + d2997 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1347, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16590 pattern childGuard
    simpa only [d1347, d2997, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1347, d2997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16593 pattern childGuard
    simpa only [d1347, d2997, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16595 (pattern : Twelve) (guard : d2746 pattern = 1) : d1330 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1330, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16550 pattern childGuard
    simpa only [d1330, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1330, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1330, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16596 (pattern : Twelve) (guard : d2746 pattern = 1) : d1331 pattern ≤ (1 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1331, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16564 pattern childGuard
    simpa only [d1331, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1331, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1331, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16597 (pattern : Twelve) (guard : d2746 pattern = 1) : d1337 pattern ≤ (1 : Int) + d2998 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1337, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16595 pattern childGuard
    simpa only [d1337, d2998, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1337, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16596 pattern childGuard
    simpa only [d1337, d2998, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16598 (pattern : Twelve) (guard : d2746 pattern = 1) : d1343 pattern ≤ (1 : Int) + d2999 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1343, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16497 pattern childGuard
    simpa only [d1343, d2999, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1343, d2999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16597 pattern childGuard
    simpa only [d1343, d2999, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16599 (pattern : Twelve) (guard : d2746 pattern = 1) : d1332 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1332, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d1332, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1332, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1332, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16600 (pattern : Twelve) (guard : d2746 pattern = 1) : d1338 pattern ≤ (1 : Int) + d3000 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1338, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16599 pattern childGuard
    simpa only [d1338, d3000, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1338, d3000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16464 pattern childGuard
    simpa only [d1338, d3000, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16601 (pattern : Twelve) (guard : d2746 pattern = 1) : d1344 pattern ≤ (1 : Int) + d3001 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1344, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16600 pattern childGuard
    simpa only [d1344, d3001, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1344, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1344, d3001, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16602 (pattern : Twelve) (guard : d2746 pattern = 1) : d1348 pattern ≤ (1 : Int) + d3002 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1348, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16598 pattern childGuard
    simpa only [d1348, d3002, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1348, d3002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16601 pattern childGuard
    simpa only [d1348, d3002, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16603 (pattern : Twelve) (guard : d2746 pattern = 1) : d1350 pattern ≤ (1 : Int) + d3003 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1350, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16594 pattern childGuard
    simpa only [d1350, d3003, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1350, d3003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16602 pattern childGuard
    simpa only [d1350, d3003, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16604 (pattern : Twelve) (guard : d2746 pattern = 1) : d1351 pattern ≤ (1 : Int) + d2986 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1351, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16586 pattern childGuard
    simpa only [d1351, d2986, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1351, d2986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1351, d2986, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16605 (pattern : Twelve) (guard : d2746 pattern = 1) : d1352 pattern ≤ (1 : Int) + d3004 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1352, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16603 pattern childGuard
    simpa only [d1352, d3004, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1352, d3004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16604 pattern childGuard
    simpa only [d1352, d3004, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16606 (pattern : Twelve) (guard : d2746 pattern = 1) : d1353 pattern ≤ (1 : Int) + d3005 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1353, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16587 pattern childGuard
    simpa only [d1353, d3005, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1353, d3005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16605 pattern childGuard
    simpa only [d1353, d3005, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16607 (pattern : Twelve) (guard : d2746 pattern = 1) : d1354 pattern ≤ (1 : Int) + d3006 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1354, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16574 pattern childGuard
    simpa only [d1354, d3006, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1354, d3006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16606 pattern childGuard
    simpa only [d1354, d3006, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16608 (pattern : Twelve) (guard : d2746 pattern = 1) : d1649 pattern ≤ (1 : Int) + d3007 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1649, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d1649, d3007, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1649, d3007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1649, d3007, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16609 (pattern : Twelve) (guard : d2746 pattern = 1) : d1650 pattern ≤ (1 : Int) + d3008 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1650, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16424 pattern childGuard
    simpa only [d1650, d3008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1650, d3008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1650, d3008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16610 (pattern : Twelve) (guard : d2746 pattern = 1) : d1656 pattern ≤ (1 : Int) + d3009 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1656, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16608 pattern childGuard
    simpa only [d1656, d3009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1656, d3009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16609 pattern childGuard
    simpa only [d1656, d3009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16611 (pattern : Twelve) (guard : d2746 pattern = 1) : d1644 pattern ≤ (1 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1644, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1644, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1644, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16381 pattern childGuard
    simpa only [d1644, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16612 (pattern : Twelve) (guard : d2746 pattern = 1) : d1645 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1645, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1645, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1645, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1645, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16613 (pattern : Twelve) (guard : d2746 pattern = 1) : d1647 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1647, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16611 pattern childGuard
    simpa only [d1647, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1647, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16612 pattern childGuard
    simpa only [d1647, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16614 (pattern : Twelve) (guard : d2746 pattern = 1) : d1651 pattern ≤ (1 : Int) + d3010 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1651, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16555 pattern childGuard
    simpa only [d1651, d3010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1651, d3010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16613 pattern childGuard
    simpa only [d1651, d3010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16615 (pattern : Twelve) (guard : d2746 pattern = 1) : d1657 pattern ≤ (1 : Int) + d3011 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1657, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16614 pattern childGuard
    simpa only [d1657, d3011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1657, d3011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16569 pattern childGuard
    simpa only [d1657, d3011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16616 (pattern : Twelve) (guard : d2746 pattern = 1) : d1660 pattern ≤ (1 : Int) + d3012 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1660, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16610 pattern childGuard
    simpa only [d1660, d3012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1660, d3012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16615 pattern childGuard
    simpa only [d1660, d3012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16617 (pattern : Twelve) (guard : d2746 pattern = 1) : d1652 pattern ≤ (1 : Int) + d3013 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1652, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d1652, d3013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1652, d3013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16611 pattern childGuard
    simpa only [d1652, d3013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16618 (pattern : Twelve) (guard : d2746 pattern = 1) : d1653 pattern ≤ (1 : Int) + d3014 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1653, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16498 pattern childGuard
    simpa only [d1653, d3014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1653, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1653, d3014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16619 (pattern : Twelve) (guard : d2746 pattern = 1) : d1658 pattern ≤ (1 : Int) + d3015 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1658, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16617 pattern childGuard
    simpa only [d1658, d3015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1658, d3015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16618 pattern childGuard
    simpa only [d1658, d3015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16620 (pattern : Twelve) (guard : d2746 pattern = 1) : d1646 pattern ≤ (1 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1646, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16381 pattern childGuard
    simpa only [d1646, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1646, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1646, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16621 (pattern : Twelve) (guard : d2746 pattern = 1) : d1648 pattern ≤ (1 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16620 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16464 pattern childGuard
    simpa only [d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16622 (pattern : Twelve) (guard : d2746 pattern = 1) : d1654 pattern ≤ (1 : Int) + d3016 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1654, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16568 pattern childGuard
    simpa only [d1654, d3016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1654, d3016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16621 pattern childGuard
    simpa only [d1654, d3016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16623 (pattern : Twelve) (guard : d2746 pattern = 1) : d1655 pattern ≤ (1 : Int) + d3017 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1655, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16499 pattern childGuard
    simpa only [d1655, d3017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1655, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1655, d3017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16624 (pattern : Twelve) (guard : d2746 pattern = 1) : d1659 pattern ≤ (1 : Int) + d3018 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1659, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16622 pattern childGuard
    simpa only [d1659, d3018, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1659, d3018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16623 pattern childGuard
    simpa only [d1659, d3018, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16625 (pattern : Twelve) (guard : d2746 pattern = 1) : d1661 pattern ≤ (1 : Int) + d3019 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1661, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16619 pattern childGuard
    simpa only [d1661, d3019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1661, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16624 pattern childGuard
    simpa only [d1661, d3019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16626 (pattern : Twelve) (guard : d2746 pattern = 1) : d1662 pattern ≤ (1 : Int) + d3020 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1662, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16615 pattern childGuard
    simpa only [d1662, d3020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1662, d3020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1662, d3020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16627 (pattern : Twelve) (guard : d2746 pattern = 1) : d1663 pattern ≤ (1 : Int) + d3021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1663, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16625 pattern childGuard
    simpa only [d1663, d3021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1663, d3021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16626 pattern childGuard
    simpa only [d1663, d3021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16628 (pattern : Twelve) (guard : d2746 pattern = 1) : d1664 pattern ≤ (1 : Int) + d3022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1664, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16616 pattern childGuard
    simpa only [d1664, d3022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1664, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16627 pattern childGuard
    simpa only [d1664, d3022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16629 (pattern : Twelve) (guard : d2746 pattern = 1) : d1668 pattern ≤ (1 : Int) + d3023 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1668, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16373 pattern childGuard
    simpa only [d1668, d3023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1668, d3023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16611 pattern childGuard
    simpa only [d1668, d3023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16630 (pattern : Twelve) (guard : d2746 pattern = 1) : d1671 pattern ≤ (1 : Int) + d3024 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1671, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16629 pattern childGuard
    simpa only [d1671, d3024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1671, d3024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16609 pattern childGuard
    simpa only [d1671, d3024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16631 (pattern : Twelve) (guard : d2746 pattern = 1) : d1674 pattern ≤ (1 : Int) + d3025 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1674, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16630 pattern childGuard
    simpa only [d1674, d3025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1674, d3025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16615 pattern childGuard
    simpa only [d1674, d3025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16632 (pattern : Twelve) (guard : d2746 pattern = 1) : d1665 pattern ≤ (1 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1665, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16577 pattern childGuard
    simpa only [d1665, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1665, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15986 pattern childGuard
    simpa only [d1665, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16633 (pattern : Twelve) (guard : d2746 pattern = 1) : d1666 pattern ≤ (1 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1666, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16611 pattern childGuard
    simpa only [d1666, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1666, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16632 pattern childGuard
    simpa only [d1666, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16634 (pattern : Twelve) (guard : d2746 pattern = 1) : d1669 pattern ≤ (1 : Int) + d3026 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1669, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16477 pattern childGuard
    simpa only [d1669, d3026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1669, d3026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16633 pattern childGuard
    simpa only [d1669, d3026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16635 (pattern : Twelve) (guard : d2746 pattern = 1) : d1672 pattern ≤ (1 : Int) + d3027 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1672, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16634 pattern childGuard
    simpa only [d1672, d3027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1672, d3027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16569 pattern childGuard
    simpa only [d1672, d3027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16636 (pattern : Twelve) (guard : d2746 pattern = 1) : d1667 pattern ≤ (1 : Int) + d786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1667, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16464 pattern childGuard
    simpa only [d1667, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1667, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16351 pattern childGuard
    simpa only [d1667, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16637 (pattern : Twelve) (guard : d2746 pattern = 1) : d1670 pattern ≤ (1 : Int) + d3028 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1670, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16568 pattern childGuard
    simpa only [d1670, d3028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1670, d3028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16636 pattern childGuard
    simpa only [d1670, d3028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16638 (pattern : Twelve) (guard : d2746 pattern = 1) : d1252 pattern ≤ (1 : Int) + d3029 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1252, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16499 pattern childGuard
    simpa only [d1252, d3029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1252, d3029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1252, d3029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16639 (pattern : Twelve) (guard : d2746 pattern = 1) : d1626 pattern ≤ (1 : Int) + d3030 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1626, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16638 pattern childGuard
    simpa only [d1626, d3030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1626, d3030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15960 pattern childGuard
    simpa only [d1626, d3030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16640 (pattern : Twelve) (guard : d2746 pattern = 1) : d1673 pattern ≤ (1 : Int) + d3031 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1673, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16637 pattern childGuard
    simpa only [d1673, d3031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1673, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16639 pattern childGuard
    simpa only [d1673, d3031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16641 (pattern : Twelve) (guard : d2746 pattern = 1) : d1675 pattern ≤ (1 : Int) + d3032 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1675, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16635 pattern childGuard
    simpa only [d1675, d3032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1675, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16640 pattern childGuard
    simpa only [d1675, d3032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16642 (pattern : Twelve) (guard : d2746 pattern = 1) : d1676 pattern ≤ (1 : Int) + d3033 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1676, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16641 pattern childGuard
    simpa only [d1676, d3033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1676, d3033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16626 pattern childGuard
    simpa only [d1676, d3033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16643 (pattern : Twelve) (guard : d2746 pattern = 1) : d1677 pattern ≤ (1 : Int) + d3034 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1677, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16631 pattern childGuard
    simpa only [d1677, d3034, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1677, d3034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16642 pattern childGuard
    simpa only [d1677, d3034, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16644 (pattern : Twelve) (guard : d2746 pattern = 1) : d1678 pattern ≤ (1 : Int) + d3035 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1678, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16628 pattern childGuard
    simpa only [d1678, d3035, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2746 pattern = 1 := by simpa only [d1678, d3035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16643 pattern childGuard
    simpa only [d1678, d3035, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16645 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11444 pattern childGuard
    simpa only [d1848, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16646 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d1 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16645 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11445 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16647 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d1859 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16646 pattern childGuard
    simpa only [d72, d1859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16648 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10900 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10863 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16649 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16648 pattern childGuard
    simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10879 pattern childGuard
    simpa only [d17, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16650 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d18 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c16651 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16649 pattern childGuard
    simpa only [d1848, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16650 pattern childGuard
    simpa only [d1848, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16652 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) ≤ (0 : Int) + 6
  decide
theorem c16653 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16652 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14969 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16654 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d6 pattern := by
  change (1 : Int) ≤ (0 : Int) + 6
  decide
theorem c16655 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16654 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15041 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16656 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16653 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16655 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16657 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16656 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1848, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16658 (pattern : Twelve) (guard : d1848 pattern = 1) : d51 pattern ≤ (0 : Int) + d2281 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16651 pattern childGuard
    simpa only [d51, d2281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16657 pattern childGuard
    simpa only [d51, d2281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16659 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d2282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d73, d2282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16658 pattern childGuard
    simpa only [d73, d2282, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
