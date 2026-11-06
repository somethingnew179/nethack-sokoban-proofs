/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3500 (p : Pattern) (guard : d1242 p = 1) : d309 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3501 (p : Pattern) (guard : d1242 p = 1) : d310 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3502 (p : Pattern) (guard : d1242 p = 1) : d311 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d311, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3491 p hg
    simpa only [d311, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d311, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3501 p hg
    simpa only [d311, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3503 (p : Pattern) (guard : d1242 p = 1) : d313 p ≤ (0 : Int) + d735 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d313, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d313, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d313, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d313, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3504 (p : Pattern) (guard : d1242 p = 1) : d314 p ≤ (0 : Int) + d736 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d314, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3502 p hg
    simpa only [d314, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d314, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3503 p hg
    simpa only [d314, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3505 (p : Pattern) (guard : d1242 p = 1) : d322 p ≤ (0 : Int) + d737 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d322, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d322, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d322, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d322, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3506 (p : Pattern) (guard : d1242 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare3507 (p : Pattern) (guard : d1242 p = 1) : d323 p ≤ (0 : Int) + d738 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d323, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3484 p hg
    simpa only [d323, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d323, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3506 p hg
    simpa only [d323, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3508 (p : Pattern) (guard : d1242 p = 1) : d324 p ≤ (0 : Int) + d739 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d324, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3505 p hg
    simpa only [d324, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d324, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3507 p hg
    simpa only [d324, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3509 (p : Pattern) (guard : d1242 p = 1) : d325 p ≤ (0 : Int) + d740 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d325, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3504 p hg
    simpa only [d325, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d325, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3508 p hg
    simpa only [d325, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3510 (p : Pattern) (guard : d1242 p = 1) : d326 p ≤ (0 : Int) + d741 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d326, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3498 p hg
    simpa only [d326, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d326, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3509 p hg
    simpa only [d326, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3511 (p : Pattern) (guard : d1242 p = 1) : d327 p ≤ (0 : Int) + d742 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d327, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3488 p hg
    simpa only [d327, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d327, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3510 p hg
    simpa only [d327, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3512 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d549 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3513 (p : Pattern) (guard : d1243 p = 1) : d293 p ≤ (0 : Int) + d550 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d293, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2358 p hg
    simpa only [d1243, d293, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d293, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3512 p hg
    simpa only [d1243, d293, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3514 (p : Pattern) (guard : d1167 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare3515 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d538 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d1171, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1171, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3516 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d539 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d1171, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3517 (p : Pattern) (guard : d1167 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare3518 (p : Pattern) (guard : d1171 p = 1) : d14 p ≤ (0 : Int) + d540 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3517 p hg
    simpa only [d1171, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1171, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3519 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d541 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3520 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3521 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3522 (p : Pattern) (guard : d1167 p = 1) : d6 p ≤ (0 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d1167, d6, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3523 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d551 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3522 p hg
    simpa only [d1171, d8, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d8, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3524 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3525 (p : Pattern) (guard : d1167 p = 1) : d12 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d1167, d12, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3526 (p : Pattern) (guard : d1171 p = 1) : d14 p ≤ (0 : Int) + d546 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d14, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3525 p hg
    simpa only [d1171, d14, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d14, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1171, d14, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3527 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d552 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d15, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d15, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d15, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d15, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3528 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d16, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d16, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3529 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d554 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3520 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3528 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3530 (p : Pattern) (guard : d1246 p = 1) : d293 p ≤ (0 : Int) + d555 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d293, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d1246, d293, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d293, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3512 p hg
    simpa only [d1246, d293, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3531 (p : Pattern) (guard : d1247 p = 1) : d293 p ≤ (0 : Int) + d556 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3530 p hg
    simpa only [d1247, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3532 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d557 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3533 (p : Pattern) (guard : d1243 p = 1) : d294 p ≤ (0 : Int) + d558 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d294, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d1243, d294, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d294, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3532 p hg
    simpa only [d1243, d294, d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3534 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d559 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3535 (p : Pattern) (guard : d1246 p = 1) : d294 p ≤ (0 : Int) + d560 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d294, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3534 p hg
    simpa only [d1246, d294, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d294, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3532 p hg
    simpa only [d1246, d294, d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3536 (p : Pattern) (guard : d1247 p = 1) : d294 p ≤ (0 : Int) + d561 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3535 p hg
    simpa only [d1247, d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3537 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d566 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3538 (p : Pattern) (guard : d1243 p = 1) : d295 p ≤ (0 : Int) + d567 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d295, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d1243, d295, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d295, d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3537 p hg
    simpa only [d1243, d295, d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3539 (p : Pattern) (guard : d1171 p = 1) : d52 p ≤ (0 : Int) + d562 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d52, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3540 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d53, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3541 (p : Pattern) (guard : d1171 p = 1) : d52 p ≤ (0 : Int) + d568 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d52, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d52, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d52, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d52, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3542 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d569 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d53, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d53, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d53, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d53, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3543 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d570 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3540 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3542 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3544 (p : Pattern) (guard : d1246 p = 1) : d295 p ≤ (0 : Int) + d571 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d295, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3543 p hg
    simpa only [d1246, d295, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d295, d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3537 p hg
    simpa only [d1246, d295, d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3545 (p : Pattern) (guard : d1247 p = 1) : d295 p ≤ (0 : Int) + d572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3538 p hg
    simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3544 p hg
    simpa only [d1247, d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3546 (p : Pattern) (guard : d1247 p = 1) : d296 p ≤ (0 : Int) + d573 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d296, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3536 p hg
    simpa only [d296, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d296, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d296, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3547 (p : Pattern) (guard : d1247 p = 1) : d297 p ≤ (0 : Int) + d574 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d297, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d297, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d297, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3546 p hg
    simpa only [d297, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3548 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3549 (p : Pattern) (guard : d1167 p = 1) : d6 p ≤ (0 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d1167, d6, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3550 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d545 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3549 p hg
    simpa only [d1171, d8, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d8, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3551 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d547 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d15, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d15, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d15, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d15, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3552 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d548 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d16, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d16, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3553 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d575 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3520 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3554 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3555 (p : Pattern) (guard : d1246 p = 1) : d293 p ≤ (0 : Int) + d581 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d293, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3553 p hg
    simpa only [d1246, d293, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d293, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3554 p hg
    simpa only [d1246, d293, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3556 (p : Pattern) (guard : d1247 p = 1) : d293 p ≤ (0 : Int) + d582 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3555 p hg
    simpa only [d1247, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3557 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d583 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3558 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d584 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3557 p hg
    simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d16, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3559 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d585 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3560 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3561 (p : Pattern) (guard : d1246 p = 1) : d298 p ≤ (0 : Int) + d587 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d298, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3559 p hg
    simpa only [d1246, d298, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d298, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3560 p hg
    simpa only [d1246, d298, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3562 (p : Pattern) (guard : d1247 p = 1) : d299 p ≤ (0 : Int) + d588 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d299, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d1247, d299, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d299, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3561 p hg
    simpa only [d1247, d299, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3563 (p : Pattern) (guard : d1247 p = 1) : d300 p ≤ (0 : Int) + d589 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d300, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3556 p hg
    simpa only [d300, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d300, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d300, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3564 (p : Pattern) (guard : d1171 p = 1) : d15 p ≤ (0 : Int) + d557 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3565 (p : Pattern) (guard : d1246 p = 1) : d294 p ≤ (0 : Int) + d590 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d294, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3564 p hg
    simpa only [d1246, d294, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d294, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1246, d294, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3566 (p : Pattern) (guard : d1247 p = 1) : d294 p ≤ (0 : Int) + d591 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3565 p hg
    simpa only [d1247, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3567 (p : Pattern) (guard : d1171 p = 1) : d52 p ≤ (0 : Int) + d564 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d52, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d52, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d52, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d52, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3568 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d565 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d53, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d53, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d53, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d53, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3569 (p : Pattern) (guard : d1171 p = 1) : d53 p ≤ (0 : Int) + d566 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3540 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3568 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3570 (p : Pattern) (guard : d1246 p = 1) : d295 p ≤ (0 : Int) + d592 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d295, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3569 p hg
    simpa only [d1246, d295, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d295, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1246, d295, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3571 (p : Pattern) (guard : d1247 p = 1) : d295 p ≤ (0 : Int) + d593 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3538 p hg
    simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d1247, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3572 (p : Pattern) (guard : d1247 p = 1) : d296 p ≤ (0 : Int) + d594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d296, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3566 p hg
    simpa only [d296, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d296, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3571 p hg
    simpa only [d296, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3573 (p : Pattern) (guard : d1247 p = 1) : d301 p ≤ (0 : Int) + d595 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d301, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3563 p hg
    simpa only [d301, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d301, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3572 p hg
    simpa only [d301, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3574 (p : Pattern) (guard : d1247 p = 1) : d302 p ≤ (0 : Int) + d596 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d302, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3547 p hg
    simpa only [d302, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d302, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3573 p hg
    simpa only [d302, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3575 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d601 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3576 (p : Pattern) (guard : d1243 p = 1) : d303 p ≤ (0 : Int) + d602 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d303, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2430 p hg
    simpa only [d1243, d303, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d303, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3575 p hg
    simpa only [d1243, d303, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3577 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d603 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3557 p hg
    simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d86, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3578 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d604 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d86, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d86, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3579 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d605 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3577 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3578 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3580 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d601 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3581 (p : Pattern) (guard : d1246 p = 1) : d304 p ≤ (0 : Int) + d606 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d304, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3579 p hg
    simpa only [d1246, d304, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d304, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d1246, d304, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3582 (p : Pattern) (guard : d1247 p = 1) : d305 p ≤ (0 : Int) + d607 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d305, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d1247, d305, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d305, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3581 p hg
    simpa only [d1247, d305, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3583 (p : Pattern) (guard : d1247 p = 1) : d306 p ≤ (0 : Int) + d608 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d306, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d306, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d306, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3582 p hg
    simpa only [d306, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3584 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d580 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3585 (p : Pattern) (guard : d1243 p = 1) : d307 p ≤ (0 : Int) + d609 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d307, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d1243, d307, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d307, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3584 p hg
    simpa only [d1243, d307, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3586 (p : Pattern) (guard : d1171 p = 1) : d97 p ≤ (0 : Int) + d576 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d97, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3587 (p : Pattern) (guard : d1171 p = 1) : d98 p ≤ (0 : Int) + d577 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3586 p hg
    simpa only [d98, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3588 (p : Pattern) (guard : d1171 p = 1) : d97 p ≤ (0 : Int) + d578 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d97, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d97, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d97, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d97, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3589 (p : Pattern) (guard : d1171 p = 1) : d98 p ≤ (0 : Int) + d579 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d98, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d98, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d98, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3588 p hg
    simpa only [d98, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3590 (p : Pattern) (guard : d1171 p = 1) : d98 p ≤ (0 : Int) + d580 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3587 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3589 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3591 (p : Pattern) (guard : d1246 p = 1) : d307 p ≤ (0 : Int) + d580 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3590 p hg
    simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3584 p hg
    simpa only [d1246, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3592 (p : Pattern) (guard : d1247 p = 1) : d307 p ≤ (0 : Int) + d610 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3585 p hg
    simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3591 p hg
    simpa only [d1247, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3593 (p : Pattern) (guard : d1247 p = 1) : d308 p ≤ (0 : Int) + d611 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d308, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3583 p hg
    simpa only [d308, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d308, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3592 p hg
    simpa only [d308, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3594 (p : Pattern) (guard : d1243 p = 1) : d304 p ≤ (0 : Int) + d613 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d304, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2449 p hg
    simpa only [d1243, d304, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d304, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d1243, d304, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3595 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d598 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d86, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3596 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d600 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d86, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d86, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3597 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d601 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3595 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3598 (p : Pattern) (guard : d1246 p = 1) : d309 p ≤ (0 : Int) + d614 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d309, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3597 p hg
    simpa only [d1246, d309, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d309, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1246, d309, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3599 (p : Pattern) (guard : d1247 p = 1) : d310 p ≤ (0 : Int) + d615 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d310, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3594 p hg
    simpa only [d1247, d310, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d310, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3598 p hg
    simpa only [d1247, d310, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3600 (p : Pattern) (guard : d1247 p = 1) : d311 p ≤ (0 : Int) + d616 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d311, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d311, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d311, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3599 p hg
    simpa only [d311, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3601 (p : Pattern) (guard : d1246 p = 1) : d307 p ≤ (0 : Int) + d617 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d307, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3590 p hg
    simpa only [d1246, d307, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d307, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1246, d307, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3602 (p : Pattern) (guard : d1247 p = 1) : d307 p ≤ (0 : Int) + d618 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3585 p hg
    simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3601 p hg
    simpa only [d1247, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3603 (p : Pattern) (guard : d1243 p = 1) : d312 p ≤ (0 : Int) + d619 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d312, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d1243, d312, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d312, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1243, d312, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3604 (p : Pattern) (guard : d1171 p = 1) : d97 p ≤ (0 : Int) + d586 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3586 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3588 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3605 (p : Pattern) (guard : d1246 p = 1) : d312 p ≤ (0 : Int) + d620 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d312, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3604 p hg
    simpa only [d1246, d312, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d312, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1246, d312, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3606 (p : Pattern) (guard : d1247 p = 1) : d312 p ≤ (0 : Int) + d621 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3603 p hg
    simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d1247, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3607 (p : Pattern) (guard : d1247 p = 1) : d313 p ≤ (0 : Int) + d622 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d313, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3602 p hg
    simpa only [d313, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d313, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d313, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3608 (p : Pattern) (guard : d1247 p = 1) : d314 p ≤ (0 : Int) + d623 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d314, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d314, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d314, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3607 p hg
    simpa only [d314, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3609 (p : Pattern) (guard : d1247 p = 1) : d315 p ≤ (0 : Int) + d624 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d315, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3593 p hg
    simpa only [d315, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d315, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3608 p hg
    simpa only [d315, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3610 (p : Pattern) (guard : d1247 p = 1) : d316 p ≤ (0 : Int) + d625 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d316, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3574 p hg
    simpa only [d316, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d316, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3609 p hg
    simpa only [d316, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3611 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d626 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3528 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3612 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (0 : Int) + d549 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3613 (p : Pattern) (guard : d1246 p = 1) : d298 p ≤ (0 : Int) + d627 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d298, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3611 p hg
    simpa only [d1246, d298, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d298, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3612 p hg
    simpa only [d1246, d298, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3614 (p : Pattern) (guard : d1247 p = 1) : d299 p ≤ (0 : Int) + d628 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d299, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d1247, d299, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d299, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3613 p hg
    simpa only [d1247, d299, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3615 (p : Pattern) (guard : d1247 p = 1) : d300 p ≤ (0 : Int) + d629 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d300, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d300, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d300, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d300, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3616 (p : Pattern) (guard : d1247 p = 1) : d301 p ≤ (0 : Int) + d630 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d301, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3615 p hg
    simpa only [d301, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d301, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3546 p hg
    simpa only [d301, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3617 (p : Pattern) (guard : d1243 p = 1) : d298 p ≤ (0 : Int) + d632 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d1243, d298, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d1243, d298, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1243, d298, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3612 p hg
    simpa only [d1243, d298, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3618 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3619 (p : Pattern) (guard : d1171 p = 1) : d16 p ≤ (0 : Int) + d549 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3620 (p : Pattern) (guard : d1246 p = 1) : d317 p ≤ (0 : Int) + d633 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d317, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3619 p hg
    simpa only [d1246, d317, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d317, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1246, d317, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3621 (p : Pattern) (guard : d1247 p = 1) : d318 p ≤ (0 : Int) + d634 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d318, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d1247, d318, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d318, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1247, d318, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3622 (p : Pattern) (guard : d1247 p = 1) : d319 p ≤ (0 : Int) + d635 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d319, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d319, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d319, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3621 p hg
    simpa only [d319, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3623 (p : Pattern) (guard : d1247 p = 1) : d320 p ≤ (0 : Int) + d636 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d320, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3622 p hg
    simpa only [d320, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d320, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3572 p hg
    simpa only [d320, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3624 (p : Pattern) (guard : d1247 p = 1) : d321 p ≤ (0 : Int) + d637 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d321, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d321, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d321, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d321, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3625 (p : Pattern) (guard : d1171 p = 1) : d8 p ≤ (0 : Int) + d638 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3626 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d86, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3625 p hg
    simpa only [d86, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d86, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d86, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3627 (p : Pattern) (guard : d1171 p = 1) : d86 p ≤ (0 : Int) + d640 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3595 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3628 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d601 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3629 (p : Pattern) (guard : d1246 p = 1) : d309 p ≤ (0 : Int) + d641 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d309, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d1246, d309, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d309, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d1246, d309, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3630 (p : Pattern) (guard : d1247 p = 1) : d310 p ≤ (0 : Int) + d642 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d310, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3594 p hg
    simpa only [d1247, d310, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d310, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3629 p hg
    simpa only [d1247, d310, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3631 (p : Pattern) (guard : d1247 p = 1) : d311 p ≤ (0 : Int) + d643 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d311, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d311, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d311, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3630 p hg
    simpa only [d311, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3632 (p : Pattern) (guard : d1246 p = 1) : d312 p ≤ (0 : Int) + d586 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3604 p hg
    simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d1246, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3633 (p : Pattern) (guard : d1247 p = 1) : d312 p ≤ (0 : Int) + d644 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1243 p = 1 := by simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3603 p hg
    simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1246 p = 1 := by simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3632 p hg
    simpa only [d1247, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3634 (p : Pattern) (guard : d1247 p = 1) : d313 p ≤ (0 : Int) + d645 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d313, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3592 p hg
    simpa only [d313, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d313, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d313, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3635 (p : Pattern) (guard : d1247 p = 1) : d314 p ≤ (0 : Int) + d646 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d314, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3631 p hg
    simpa only [d314, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d314, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3634 p hg
    simpa only [d314, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3636 (p : Pattern) (guard : d1247 p = 1) : d322 p ≤ (0 : Int) + d647 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d322, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3621 p hg
    simpa only [d322, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d322, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3571 p hg
    simpa only [d322, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3637 (p : Pattern) (guard : d1247 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare3638 (p : Pattern) (guard : d1247 p = 1) : d323 p ≤ (0 : Int) + d648 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d323, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d323, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d323, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3637 p hg
    simpa only [d323, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3639 (p : Pattern) (guard : d1247 p = 1) : d324 p ≤ (0 : Int) + d649 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1247 p = 1 := by simpa only [d324, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3636 p hg
    simpa only [d324, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1247 p = 1 := by simpa only [d324, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3638 p hg
    simpa only [d324, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
