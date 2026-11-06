/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25480 (p : Pattern) (guard : d5540 p = 1) : d2964 p ≤ (2 : Int) + d6116 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2964, d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2964, d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2964, d6116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25479 p hg
    simpa only [d2964, d6116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25481 (p : Pattern) (guard : d5540 p = 1) : d2965 p ≤ (2 : Int) + d6117 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2965, d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d2965, d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2965, d6117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d2965, d6117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25482 (p : Pattern) (guard : d5540 p = 1) : d2966 p ≤ (2 : Int) + d6118 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2966, d6118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25481 p hg
    simpa only [d2966, d6118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2966, d6118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2966, d6118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25483 (p : Pattern) (guard : d5540 p = 1) : d2967 p ≤ (2 : Int) + d6119 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2967, d6119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25475 p hg
    simpa only [d2967, d6119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2967, d6119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d2967, d6119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25484 (p : Pattern) (guard : d5540 p = 1) : d2968 p ≤ (2 : Int) + d6120 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2968, d6120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d2968, d6120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2968, d6120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2968, d6120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25485 (p : Pattern) (guard : d5540 p = 1) : d2969 p ≤ (2 : Int) + d6121 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2969, d6121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2969, d6121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2969, d6121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d2969, d6121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25486 (p : Pattern) (guard : d5540 p = 1) : d2970 p ≤ (2 : Int) + d6122 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2970, d6122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25484 p hg
    simpa only [d2970, d6122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2970, d6122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d2970, d6122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25487 (p : Pattern) (guard : d5540 p = 1) : d2971 p ≤ (2 : Int) + d6123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2971, d6123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2971, d6123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2971, d6123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d2971, d6123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25488 (p : Pattern) (guard : d5540 p = 1) : d2972 p ≤ (2 : Int) + d6124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2972, d6124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d2972, d6124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2972, d6124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d2972, d6124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25489 (p : Pattern) (guard : d5540 p = 1) : d2973 p ≤ (2 : Int) + d6125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2973, d6125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25486 p hg
    simpa only [d2973, d6125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2973, d6125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25488 p hg
    simpa only [d2973, d6125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25490 (p : Pattern) (guard : d5540 p = 1) : d2974 p ≤ (2 : Int) + d6126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2974, d6126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25479 p hg
    simpa only [d2974, d6126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2974, d6126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2974, d6126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25491 (p : Pattern) (guard : d5540 p = 1) : d2975 p ≤ (2 : Int) + d6127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2975, d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25490 p hg
    simpa only [d2975, d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2975, d6127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2975, d6127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25492 (p : Pattern) (guard : d5540 p = 1) : d2976 p ≤ (2 : Int) + d6128 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2976, d6128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25491 p hg
    simpa only [d2976, d6128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2976, d6128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2976, d6128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25493 (p : Pattern) (guard : d5540 p = 1) : d2977 p ≤ (2 : Int) + d6129 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2977, d6129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25489 p hg
    simpa only [d2977, d6129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2977, d6129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25492 p hg
    simpa only [d2977, d6129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25494 (p : Pattern) (guard : d5540 p = 1) : d2978 p ≤ (2 : Int) + d6130 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2978, d6130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25483 p hg
    simpa only [d2978, d6130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2978, d6130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d2978, d6130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25495 (p : Pattern) (guard : d5540 p = 1) : d2979 p ≤ (2 : Int) + d6131 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2979, d6131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25451 p hg
    simpa only [d2979, d6131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2979, d6131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25494 p hg
    simpa only [d2979, d6131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25496 (p : Pattern) (guard : d5540 p = 1) : d2980 p ≤ (2 : Int) + d6132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2980, d6132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d2980, d6132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2980, d6132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d2980, d6132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25497 (p : Pattern) (guard : d5540 p = 1) : d2981 p ≤ (2 : Int) + d6133 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2981, d6133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d2981, d6133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2981, d6133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d2981, d6133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25498 (p : Pattern) (guard : d5540 p = 1) : d2982 p ≤ (2 : Int) + d6134 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2982, d6134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d2982, d6134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2982, d6134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2982, d6134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25499 (p : Pattern) (guard : d5540 p = 1) : d2983 p ≤ (2 : Int) + d6135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2983, d6135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25497 p hg
    simpa only [d2983, d6135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2983, d6135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d2983, d6135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25500 (p : Pattern) (guard : d5540 p = 1) : d2984 p ≤ (2 : Int) + d6136 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2984, d6136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d2984, d6136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2984, d6136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2984, d6136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25501 (p : Pattern) (guard : d5540 p = 1) : d2985 p ≤ (2 : Int) + d6137 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2985, d6137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25499 p hg
    simpa only [d2985, d6137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2985, d6137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2985, d6137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25502 (p : Pattern) (guard : d5540 p = 1) : d2986 p ≤ (2 : Int) + d6138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2986, d6138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2986, d6138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2986, d6138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2986, d6138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25503 (p : Pattern) (guard : d5540 p = 1) : d2987 p ≤ (2 : Int) + d6139 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2987, d6139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25501 p hg
    simpa only [d2987, d6139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2987, d6139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25502 p hg
    simpa only [d2987, d6139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25504 (p : Pattern) (guard : d5540 p = 1) : d2988 p ≤ (2 : Int) + d6140 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2988, d6140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25494 p hg
    simpa only [d2988, d6140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2988, d6140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25503 p hg
    simpa only [d2988, d6140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25505 (p : Pattern) (guard : d5540 p = 1) : d2989 p ≤ (2 : Int) + d6141 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2989, d6141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25495 p hg
    simpa only [d2989, d6141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2989, d6141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25504 p hg
    simpa only [d2989, d6141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25506 (p : Pattern) (guard : d5540 p = 1) : d2990 p ≤ (2 : Int) + d6142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2990, d6142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25494 p hg
    simpa only [d2990, d6142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2990, d6142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2990, d6142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25507 (p : Pattern) (guard : d5540 p = 1) : d2991 p ≤ (2 : Int) + d6143 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2991, d6143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25495 p hg
    simpa only [d2991, d6143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2991, d6143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25506 p hg
    simpa only [d2991, d6143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25508 (p : Pattern) (guard : d5540 p = 1) : d2992 p ≤ (2 : Int) + d6144 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2992, d6144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d2992, d6144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2992, d6144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25507 p hg
    simpa only [d2992, d6144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25509 (p : Pattern) (guard : d5540 p = 1) : d103 p ≤ (2 : Int) + d103 p := by
  omega
theorem compare25510 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25511 (p : Pattern) (guard : d5501 p = 1) : d1941 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d5501, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24568 p hg
    simpa only [d5501, d1941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25512 (p : Pattern) (guard : d0 p = 1) : d1940 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25513 (p : Pattern) (guard : d5540 p = 1) : d1942 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25511 p hg
    simpa only [d5540, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d5540, d1942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25514 (p : Pattern) (guard : d5540 p = 1) : d2993 p ≤ (2 : Int) + d6145 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2993, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d2993, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2993, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25513 p hg
    simpa only [d2993, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25515 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (2 : Int) + d1873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25516 (p : Pattern) (guard : d1 p = 1) : d1873 p ≤ (2 : Int) + d1873 p := by
  omega
theorem compare25517 (p : Pattern) (guard : d5501 p = 1) : d1874 p ≤ (2 : Int) + d1873 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25515 p hg
    simpa only [d5501, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25516 p hg
    simpa only [d5501, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25518 (p : Pattern) (guard : d0 p = 1) : d1873 p ≤ (2 : Int) + d1873 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25519 (p : Pattern) (guard : d5540 p = 1) : d1875 p ≤ (2 : Int) + d1873 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d5540, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25518 p hg
    simpa only [d5540, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25520 (p : Pattern) (guard : d5540 p = 1) : d1876 p ≤ (2 : Int) + d6146 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1876, d6146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25519 p hg
    simpa only [d1876, d6146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1876, d6146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1876, d6146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25521 (p : Pattern) (guard : d5540 p = 1) : d2994 p ≤ (2 : Int) + d6147 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2994, d6147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d2994, d6147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2994, d6147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25520 p hg
    simpa only [d2994, d6147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25522 (p : Pattern) (guard : d5540 p = 1) : d107 p ≤ (2 : Int) + d107 p := by
  omega
theorem compare25523 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d1964 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25524 (p : Pattern) (guard : d5501 p = 1) : d2129 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25523 p hg
    simpa only [d5501, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24832 p hg
    simpa only [d5501, d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25525 (p : Pattern) (guard : d0 p = 1) : d1964 p ≤ (2 : Int) + d1964 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25526 (p : Pattern) (guard : d5540 p = 1) : d2130 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25524 p hg
    simpa only [d5540, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25525 p hg
    simpa only [d5540, d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25527 (p : Pattern) (guard : d5540 p = 1) : d2995 p ≤ (2 : Int) + d6148 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2995, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25522 p hg
    simpa only [d2995, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2995, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25526 p hg
    simpa only [d2995, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25528 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (2 : Int) + d1881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25529 (p : Pattern) (guard : d1 p = 1) : d1881 p ≤ (2 : Int) + d1881 p := by
  omega
theorem compare25530 (p : Pattern) (guard : d5501 p = 1) : d1882 p ≤ (2 : Int) + d1881 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25528 p hg
    simpa only [d5501, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25529 p hg
    simpa only [d5501, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25531 (p : Pattern) (guard : d0 p = 1) : d1881 p ≤ (2 : Int) + d1881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25532 (p : Pattern) (guard : d5540 p = 1) : d1883 p ≤ (2 : Int) + d1881 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25530 p hg
    simpa only [d5540, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25531 p hg
    simpa only [d5540, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25533 (p : Pattern) (guard : d5540 p = 1) : d1884 p ≤ (2 : Int) + d6149 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1884, d6149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25532 p hg
    simpa only [d1884, d6149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1884, d6149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1884, d6149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25534 (p : Pattern) (guard : d5540 p = 1) : d2996 p ≤ (2 : Int) + d6150 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2996, d6150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d2996, d6150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2996, d6150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25533 p hg
    simpa only [d2996, d6150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25535 (p : Pattern) (guard : d5540 p = 1) : d2997 p ≤ (2 : Int) + d6151 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2997, d6151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25521 p hg
    simpa only [d2997, d6151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2997, d6151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d2997, d6151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25536 (p : Pattern) (guard : d5540 p = 1) : d2998 p ≤ (2 : Int) + d6152 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2998, d6152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25521 p hg
    simpa only [d2998, d6152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2998, d6152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25535 p hg
    simpa only [d2998, d6152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25537 (p : Pattern) (guard : d5540 p = 1) : d2999 p ≤ (2 : Int) + d6153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2999, d6153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d2999, d6153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2999, d6153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d2999, d6153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25538 (p : Pattern) (guard : d5540 p = 1) : d3000 p ≤ (2 : Int) + d6154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3000, d6154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25535 p hg
    simpa only [d3000, d6154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3000, d6154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25537 p hg
    simpa only [d3000, d6154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25539 (p : Pattern) (guard : d5540 p = 1) : d3001 p ≤ (2 : Int) + d6155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3001, d6155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25536 p hg
    simpa only [d3001, d6155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3001, d6155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25538 p hg
    simpa only [d3001, d6155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25540 (p : Pattern) (guard : d5501 p = 1) : d1947 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d5501, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24566 p hg
    simpa only [d5501, d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25541 (p : Pattern) (guard : d0 p = 1) : d1956 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25542 (p : Pattern) (guard : d5540 p = 1) : d1957 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25540 p hg
    simpa only [d5540, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25541 p hg
    simpa only [d5540, d1957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25543 (p : Pattern) (guard : d5540 p = 1) : d3002 p ≤ (2 : Int) + d6145 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3002, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d3002, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3002, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25542 p hg
    simpa only [d3002, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25544 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25545 (p : Pattern) (guard : d5501 p = 1) : d1893 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d5501, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24819 p hg
    simpa only [d5501, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25546 (p : Pattern) (guard : d0 p = 1) : d1897 p ≤ (2 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25547 (p : Pattern) (guard : d5540 p = 1) : d1898 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25545 p hg
    simpa only [d5540, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25546 p hg
    simpa only [d5540, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25548 (p : Pattern) (guard : d5540 p = 1) : d1899 p ≤ (2 : Int) + d6156 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1899, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25547 p hg
    simpa only [d1899, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1899, d6156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1899, d6156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25549 (p : Pattern) (guard : d5540 p = 1) : d3003 p ≤ (2 : Int) + d6157 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3003, d6157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25543 p hg
    simpa only [d3003, d6157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3003, d6157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25548 p hg
    simpa only [d3003, d6157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25550 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (2 : Int) + d1903 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25551 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15979 p hg
    simpa only [d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25552 (p : Pattern) (guard : d1 p = 1) : d317 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25551 p hg
    simpa only [d317, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d317, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25553 (p : Pattern) (guard : d5501 p = 1) : d1901 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25550 p hg
    simpa only [d5501, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25552 p hg
    simpa only [d5501, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25554 (p : Pattern) (guard : d0 p = 1) : d1904 p ≤ (2 : Int) + d1903 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25555 (p : Pattern) (guard : d5540 p = 1) : d1905 p ≤ (2 : Int) + d1903 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25553 p hg
    simpa only [d5540, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25554 p hg
    simpa only [d5540, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25556 (p : Pattern) (guard : d5540 p = 1) : d1906 p ≤ (2 : Int) + d6158 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1906, d6158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25555 p hg
    simpa only [d1906, d6158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1906, d6158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1906, d6158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25557 (p : Pattern) (guard : d5540 p = 1) : d3004 p ≤ (2 : Int) + d6159 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3004, d6159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25543 p hg
    simpa only [d3004, d6159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3004, d6159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25556 p hg
    simpa only [d3004, d6159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25558 (p : Pattern) (guard : d5540 p = 1) : d3005 p ≤ (2 : Int) + d6160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3005, d6160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25549 p hg
    simpa only [d3005, d6160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3005, d6160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25557 p hg
    simpa only [d3005, d6160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25559 (p : Pattern) (guard : d5540 p = 1) : d3006 p ≤ (2 : Int) + d6161 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3006, d6161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25543 p hg
    simpa only [d3006, d6161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3006, d6161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3006, d6161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25560 (p : Pattern) (guard : d5501 p = 1) : d1962 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25523 p hg
    simpa only [d5501, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24830 p hg
    simpa only [d5501, d1962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25561 (p : Pattern) (guard : d0 p = 1) : d1965 p ≤ (2 : Int) + d1964 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25562 (p : Pattern) (guard : d5540 p = 1) : d1966 p ≤ (2 : Int) + d1964 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d5540, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25561 p hg
    simpa only [d5540, d1966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25563 (p : Pattern) (guard : d5540 p = 1) : d3007 p ≤ (2 : Int) + d6148 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3007, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25522 p hg
    simpa only [d3007, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3007, d6148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25562 p hg
    simpa only [d3007, d6148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25564 (p : Pattern) (guard : d5540 p = 1) : d3008 p ≤ (2 : Int) + d6162 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3008, d6162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25563 p hg
    simpa only [d3008, d6162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3008, d6162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3008, d6162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25565 (p : Pattern) (guard : d5540 p = 1) : d3009 p ≤ (2 : Int) + d6163 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3009, d6163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25559 p hg
    simpa only [d3009, d6163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3009, d6163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d3009, d6163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25566 (p : Pattern) (guard : d5540 p = 1) : d3010 p ≤ (2 : Int) + d6164 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3010, d6164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25558 p hg
    simpa only [d3010, d6164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3010, d6164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25565 p hg
    simpa only [d3010, d6164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25567 (p : Pattern) (guard : d5540 p = 1) : d3011 p ≤ (2 : Int) + d6165 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3011, d6165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25444 p hg
    simpa only [d3011, d6165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3011, d6165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3011, d6165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25568 (p : Pattern) (guard : d5540 p = 1) : d3012 p ≤ (2 : Int) + d6166 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3012, d6166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25565 p hg
    simpa only [d3012, d6166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3012, d6166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25567 p hg
    simpa only [d3012, d6166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25569 (p : Pattern) (guard : d5540 p = 1) : d3013 p ≤ (2 : Int) + d6167 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3013, d6167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25566 p hg
    simpa only [d3013, d6167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3013, d6167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25568 p hg
    simpa only [d3013, d6167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25570 (p : Pattern) (guard : d5540 p = 1) : d3014 p ≤ (2 : Int) + d6168 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3014, d6168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25539 p hg
    simpa only [d3014, d6168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3014, d6168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25569 p hg
    simpa only [d3014, d6168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25571 (p : Pattern) (guard : d5540 p = 1) : d116 p ≤ (2 : Int) + d116 p := by
  omega
theorem compare25572 (p : Pattern) (guard : d5501 p = 1) : d2124 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d5501, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24821 p hg
    simpa only [d5501, d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25573 (p : Pattern) (guard : d0 p = 1) : d1895 p ≤ (2 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25574 (p : Pattern) (guard : d5540 p = 1) : d2125 p ≤ (2 : Int) + d1895 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25572 p hg
    simpa only [d5540, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25573 p hg
    simpa only [d5540, d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25575 (p : Pattern) (guard : d5540 p = 1) : d3015 p ≤ (2 : Int) + d6169 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3015, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25571 p hg
    simpa only [d3015, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3015, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25574 p hg
    simpa only [d3015, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25576 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (2 : Int) + d1919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25577 (p : Pattern) (guard : d1 p = 1) : d1919 p ≤ (2 : Int) + d1919 p := by
  omega
theorem compare25578 (p : Pattern) (guard : d5501 p = 1) : d1920 p ≤ (2 : Int) + d1919 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25576 p hg
    simpa only [d5501, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25577 p hg
    simpa only [d5501, d1920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25579 (p : Pattern) (guard : d0 p = 1) : d1919 p ≤ (2 : Int) + d1919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25580 (p : Pattern) (guard : d5540 p = 1) : d1921 p ≤ (2 : Int) + d1919 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25578 p hg
    simpa only [d5540, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25579 p hg
    simpa only [d5540, d1921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25581 (p : Pattern) (guard : d5540 p = 1) : d1922 p ≤ (2 : Int) + d6170 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1922, d6170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25580 p hg
    simpa only [d1922, d6170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1922, d6170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1922, d6170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25582 (p : Pattern) (guard : d5540 p = 1) : d3016 p ≤ (2 : Int) + d6171 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3016, d6171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25575 p hg
    simpa only [d3016, d6171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3016, d6171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25581 p hg
    simpa only [d3016, d6171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25583 (p : Pattern) (guard : d5540 p = 1) : d3017 p ≤ (2 : Int) + d6172 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3017, d6172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25521 p hg
    simpa only [d3017, d6172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3017, d6172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25582 p hg
    simpa only [d3017, d6172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25584 (p : Pattern) (guard : d5540 p = 1) : d3018 p ≤ (2 : Int) + d6173 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3018, d6173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d3018, d6173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3018, d6173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d3018, d6173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25585 (p : Pattern) (guard : d5540 p = 1) : d3019 p ≤ (2 : Int) + d6174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3019, d6174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d3019, d6174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3019, d6174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25584 p hg
    simpa only [d3019, d6174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25586 (p : Pattern) (guard : d5540 p = 1) : d3020 p ≤ (2 : Int) + d6175 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3020, d6175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25534 p hg
    simpa only [d3020, d6175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3020, d6175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d3020, d6175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25587 (p : Pattern) (guard : d5540 p = 1) : d3021 p ≤ (2 : Int) + d6176 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3021, d6176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25586 p hg
    simpa only [d3021, d6176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3021, d6176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3021, d6176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25588 (p : Pattern) (guard : d5540 p = 1) : d3022 p ≤ (2 : Int) + d6177 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3022, d6177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25585 p hg
    simpa only [d3022, d6177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3022, d6177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25587 p hg
    simpa only [d3022, d6177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25589 (p : Pattern) (guard : d5540 p = 1) : d3023 p ≤ (2 : Int) + d6169 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3023, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25571 p hg
    simpa only [d3023, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3023, d6169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25547 p hg
    simpa only [d3023, d6169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25590 (p : Pattern) (guard : d5540 p = 1) : d3024 p ≤ (2 : Int) + d6178 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3024, d6178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25589 p hg
    simpa only [d3024, d6178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3024, d6178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3024, d6178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25591 (p : Pattern) (guard : d5540 p = 1) : d3025 p ≤ (2 : Int) + d6179 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3025, d6179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25557 p hg
    simpa only [d3025, d6179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3025, d6179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25590 p hg
    simpa only [d3025, d6179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25592 (p : Pattern) (guard : d5540 p = 1) : d3026 p ≤ (2 : Int) + d6180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3026, d6180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d3026, d6180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3026, d6180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25444 p hg
    simpa only [d3026, d6180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25593 (p : Pattern) (guard : d5540 p = 1) : d3027 p ≤ (2 : Int) + d6181 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3027, d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25591 p hg
    simpa only [d3027, d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3027, d6181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25592 p hg
    simpa only [d3027, d6181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25594 (p : Pattern) (guard : d5540 p = 1) : d3028 p ≤ (2 : Int) + d6182 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3028, d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25564 p hg
    simpa only [d3028, d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3028, d6182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25446 p hg
    simpa only [d3028, d6182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25595 (p : Pattern) (guard : d5540 p = 1) : d3029 p ≤ (2 : Int) + d6183 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3029, d6183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25594 p hg
    simpa only [d3029, d6183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3029, d6183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d3029, d6183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25596 (p : Pattern) (guard : d5540 p = 1) : d3030 p ≤ (2 : Int) + d6184 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3030, d6184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25593 p hg
    simpa only [d3030, d6184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3030, d6184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25595 p hg
    simpa only [d3030, d6184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25597 (p : Pattern) (guard : d5540 p = 1) : d3031 p ≤ (2 : Int) + d6185 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3031, d6185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25588 p hg
    simpa only [d3031, d6185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3031, d6185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25596 p hg
    simpa only [d3031, d6185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25598 (p : Pattern) (guard : d5540 p = 1) : d3032 p ≤ (2 : Int) + d6186 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3032, d6186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25570 p hg
    simpa only [d3032, d6186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3032, d6186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25597 p hg
    simpa only [d3032, d6186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25599 (p : Pattern) (guard : d0 p = 1) : d2107 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25600 (p : Pattern) (guard : d5540 p = 1) : d2108 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25540 p hg
    simpa only [d5540, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25599 p hg
    simpa only [d5540, d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25601 (p : Pattern) (guard : d5540 p = 1) : d3033 p ≤ (2 : Int) + d6145 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3033, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d3033, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3033, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25600 p hg
    simpa only [d3033, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25602 (p : Pattern) (guard : d5540 p = 1) : d1943 p ≤ (2 : Int) + d6187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1943, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25513 p hg
    simpa only [d1943, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1943, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1943, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25603 (p : Pattern) (guard : d5540 p = 1) : d3034 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3034, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25601 p hg
    simpa only [d3034, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3034, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25602 p hg
    simpa only [d3034, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25604 (p : Pattern) (guard : d0 p = 1) : d3037 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25605 (p : Pattern) (guard : d5540 p = 1) : d3038 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25540 p hg
    simpa only [d5540, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d3038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25604 p hg
    simpa only [d5540, d3038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25606 (p : Pattern) (guard : d5540 p = 1) : d3039 p ≤ (2 : Int) + d6145 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3039, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25509 p hg
    simpa only [d3039, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3039, d6145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25605 p hg
    simpa only [d3039, d6145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25607 (p : Pattern) (guard : d0 p = 1) : d1950 p ≤ (2 : Int) + d1940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25608 (p : Pattern) (guard : d5540 p = 1) : d1951 p ≤ (2 : Int) + d1940 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25540 p hg
    simpa only [d5540, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25607 p hg
    simpa only [d5540, d1951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25609 (p : Pattern) (guard : d5540 p = 1) : d1952 p ≤ (2 : Int) + d6187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1952, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25608 p hg
    simpa only [d1952, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1952, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1952, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25610 (p : Pattern) (guard : d5540 p = 1) : d3040 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3040, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25606 p hg
    simpa only [d3040, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3040, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25609 p hg
    simpa only [d3040, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25611 (p : Pattern) (guard : d5540 p = 1) : d3041 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25603 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25610 p hg
    simpa only [d3041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25612 (p : Pattern) (guard : d5540 p = 1) : d1958 p ≤ (2 : Int) + d6187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1958, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25542 p hg
    simpa only [d1958, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1958, d6187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1958, d6187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25613 (p : Pattern) (guard : d5540 p = 1) : d3042 p ≤ (2 : Int) + d6188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3042, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25543 p hg
    simpa only [d3042, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3042, d6188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25612 p hg
    simpa only [d3042, d6188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25614 (p : Pattern) (guard : d5540 p = 1) : d1967 p ≤ (2 : Int) + d6189 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1967, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25562 p hg
    simpa only [d1967, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1967, d6189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1967, d6189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25615 (p : Pattern) (guard : d5540 p = 1) : d3043 p ≤ (2 : Int) + d6190 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3043, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25563 p hg
    simpa only [d3043, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3043, d6190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25614 p hg
    simpa only [d3043, d6190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25616 (p : Pattern) (guard : d5540 p = 1) : d3044 p ≤ (2 : Int) + d6191 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3044, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25613 p hg
    simpa only [d3044, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3044, d6191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25615 p hg
    simpa only [d3044, d6191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25617 (p : Pattern) (guard : d5540 p = 1) : d3045 p ≤ (2 : Int) + d6192 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3045, d6192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25611 p hg
    simpa only [d3045, d6192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3045, d6192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25616 p hg
    simpa only [d3045, d6192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25618 (p : Pattern) (guard : d5540 p = 1) : d3046 p ≤ (2 : Int) + d6193 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3046, d6193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25616 p hg
    simpa only [d3046, d6193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3046, d6193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25537 p hg
    simpa only [d3046, d6193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25619 (p : Pattern) (guard : d5540 p = 1) : d3047 p ≤ (2 : Int) + d6194 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d3047, d6194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25617 p hg
    simpa only [d3047, d6194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d3047, d6194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25618 p hg
    simpa only [d3047, d6194, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
