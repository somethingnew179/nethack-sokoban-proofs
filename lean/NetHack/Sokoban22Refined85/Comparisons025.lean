/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3500 (p : Pattern) (guard : d4077 p = 1) : d691 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3501 (p : Pattern) (guard : d4077 p = 1) : d692 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3491 p hg
    simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3502 (p : Pattern) (guard : d4077 p = 1) : d693 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3501 p hg
    simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3503 (p : Pattern) (guard : d4077 p = 1) : d694 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3502 p hg
    simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3504 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (0 : Int) + d219 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3505 (p : Pattern) (guard : d4077 p = 1) : d695 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3504 p hg
    simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3506 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (0 : Int) + d221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3507 (p : Pattern) (guard : d4077 p = 1) : d696 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3506 p hg
    simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3508 (p : Pattern) (guard : d4077 p = 1) : d697 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3505 p hg
    simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3507 p hg
    simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3509 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (0 : Int) + d221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3510 (p : Pattern) (guard : d4077 p = 1) : d698 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3509 p hg
    simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3511 (p : Pattern) (guard : d4077 p = 1) : d699 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3510 p hg
    simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3512 (p : Pattern) (guard : d4077 p = 1) : d700 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3508 p hg
    simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3511 p hg
    simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3513 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (0 : Int) + d289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3514 (p : Pattern) (guard : d4077 p = 1) : d701 p ≤ (0 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2306 p hg
    simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3515 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3516 (p : Pattern) (guard : d4077 p = 1) : d702 p ≤ (0 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2309 p hg
    simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3517 (p : Pattern) (guard : d4077 p = 1) : d703 p ≤ (0 : Int) + d306 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3518 (p : Pattern) (guard : d4077 p = 1) : d704 p ≤ (0 : Int) + d307 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3519 (p : Pattern) (guard : d4077 p = 1) : d705 p ≤ (0 : Int) + d308 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3517 p hg
    simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3520 (p : Pattern) (guard : d4077 p = 1) : d706 p ≤ (0 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3512 p hg
    simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3521 (p : Pattern) (guard : d4077 p = 1) : d707 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3520 p hg
    simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3522 (p : Pattern) (guard : d4077 p = 1) : d708 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3523 (p : Pattern) (guard : d4077 p = 1) : d709 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3503 p hg
    simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3522 p hg
    simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3524 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (2 : Int) + d52 p := by
  omega
theorem compare3525 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (2 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3526 (p : Pattern) (guard : d4077 p = 1) : d653 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3525 p hg
    simpa only [d4077, d653, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3527 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (2 : Int) + d82 p := by
  omega
theorem compare3528 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3529 (p : Pattern) (guard : d4077 p = 1) : d654 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3528 p hg
    simpa only [d4077, d654, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3530 (p : Pattern) (guard : d4077 p = 1) : d655 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d655, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3531 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3532 (p : Pattern) (guard : d4077 p = 1) : d656 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d4077, d656, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3533 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (2 : Int) + d94 p := by
  omega
theorem compare3534 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (2 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3535 (p : Pattern) (guard : d4077 p = 1) : d657 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3534 p hg
    simpa only [d4077, d657, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3536 (p : Pattern) (guard : d4077 p = 1) : d658 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3532 p hg
    simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3535 p hg
    simpa only [d658, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3537 (p : Pattern) (guard : d4077 p = 1) : d659 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3530 p hg
    simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3536 p hg
    simpa only [d659, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3538 (p : Pattern) (guard : d0 p = 1) : d397 p ≤ (2 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3539 (p : Pattern) (guard : d4077 p = 1) : d660 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3538 p hg
    simpa only [d4077, d660, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3540 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3541 (p : Pattern) (guard : d4077 p = 1) : d661 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3540 p hg
    simpa only [d4077, d661, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3542 (p : Pattern) (guard : d4077 p = 1) : d662 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d662, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3543 (p : Pattern) (guard : d0 p = 1) : d410 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3544 (p : Pattern) (guard : d4077 p = 1) : d663 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3543 p hg
    simpa only [d4077, d663, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3545 (p : Pattern) (guard : d4077 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare3546 (p : Pattern) (guard : d4077 p = 1) : d664 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3544 p hg
    simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d664, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3547 (p : Pattern) (guard : d4077 p = 1) : d665 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3542 p hg
    simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3546 p hg
    simpa only [d665, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3548 (p : Pattern) (guard : d4077 p = 1) : d666 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3537 p hg
    simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3547 p hg
    simpa only [d666, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3549 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (2 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3550 (p : Pattern) (guard : d4077 p = 1) : d667 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3549 p hg
    simpa only [d4077, d667, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3551 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3552 (p : Pattern) (guard : d4077 p = 1) : d668 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d4077, d668, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3553 (p : Pattern) (guard : d4077 p = 1) : d669 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d669, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3554 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3555 (p : Pattern) (guard : d4077 p = 1) : d670 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3554 p hg
    simpa only [d4077, d670, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3556 (p : Pattern) (guard : d4077 p = 1) : d671 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3555 p hg
    simpa only [d671, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3557 (p : Pattern) (guard : d4077 p = 1) : d672 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3553 p hg
    simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3556 p hg
    simpa only [d672, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3558 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (2 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3559 (p : Pattern) (guard : d4077 p = 1) : d673 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d4077, d673, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3560 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3561 (p : Pattern) (guard : d4077 p = 1) : d674 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3560 p hg
    simpa only [d4077, d674, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3562 (p : Pattern) (guard : d4077 p = 1) : d675 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3559 p hg
    simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3561 p hg
    simpa only [d675, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3563 (p : Pattern) (guard : d4077 p = 1) : d676 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d676, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3564 (p : Pattern) (guard : d4077 p = 1) : d677 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3563 p hg
    simpa only [d677, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3565 (p : Pattern) (guard : d4077 p = 1) : d678 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3557 p hg
    simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3564 p hg
    simpa only [d678, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3566 (p : Pattern) (guard : d4077 p = 1) : d679 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3565 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3567 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (2 : Int) + d131 p := by
  omega
theorem compare3568 (p : Pattern) (guard : d0 p = 1) : d418 p ≤ (2 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3569 (p : Pattern) (guard : d4077 p = 1) : d680 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3568 p hg
    simpa only [d4077, d680, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3570 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (2 : Int) + d152 p := by
  omega
theorem compare3571 (p : Pattern) (guard : d0 p = 1) : d420 p ≤ (2 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3572 (p : Pattern) (guard : d4077 p = 1) : d681 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3571 p hg
    simpa only [d4077, d681, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3573 (p : Pattern) (guard : d4077 p = 1) : d682 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3569 p hg
    simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3572 p hg
    simpa only [d682, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3574 (p : Pattern) (guard : d0 p = 1) : d399 p ≤ (2 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3575 (p : Pattern) (guard : d4077 p = 1) : d683 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3574 p hg
    simpa only [d4077, d683, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3576 (p : Pattern) (guard : d4077 p = 1) : d162 p ≤ (2 : Int) + d162 p := by
  omega
theorem compare3577 (p : Pattern) (guard : d4077 p = 1) : d684 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3575 p hg
    simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d684, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3578 (p : Pattern) (guard : d4077 p = 1) : d685 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3573 p hg
    simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3577 p hg
    simpa only [d685, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3579 (p : Pattern) (guard : d0 p = 1) : d407 p ≤ (2 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3580 (p : Pattern) (guard : d4077 p = 1) : d686 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3579 p hg
    simpa only [d4077, d686, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3581 (p : Pattern) (guard : d0 p = 1) : d411 p ≤ (2 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3582 (p : Pattern) (guard : d4077 p = 1) : d687 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3581 p hg
    simpa only [d4077, d687, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3583 (p : Pattern) (guard : d4077 p = 1) : d688 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3582 p hg
    simpa only [d688, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3584 (p : Pattern) (guard : d0 p = 1) : d421 p ≤ (2 : Int) + d156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3585 (p : Pattern) (guard : d4077 p = 1) : d689 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3584 p hg
    simpa only [d4077, d689, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3586 (p : Pattern) (guard : d4077 p = 1) : d690 p ≤ (2 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3585 p hg
    simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d690, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3587 (p : Pattern) (guard : d4077 p = 1) : d691 p ≤ (2 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3583 p hg
    simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3586 p hg
    simpa only [d691, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3588 (p : Pattern) (guard : d4077 p = 1) : d692 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3578 p hg
    simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3587 p hg
    simpa only [d692, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3589 (p : Pattern) (guard : d4077 p = 1) : d693 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3588 p hg
    simpa only [d693, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3590 (p : Pattern) (guard : d4077 p = 1) : d694 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3566 p hg
    simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3589 p hg
    simpa only [d694, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3591 (p : Pattern) (guard : d0 p = 1) : d453 p ≤ (2 : Int) + d219 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3592 (p : Pattern) (guard : d4077 p = 1) : d695 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3591 p hg
    simpa only [d4077, d695, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3593 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (2 : Int) + d221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3594 (p : Pattern) (guard : d4077 p = 1) : d696 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3593 p hg
    simpa only [d4077, d696, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3595 (p : Pattern) (guard : d4077 p = 1) : d697 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3592 p hg
    simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3594 p hg
    simpa only [d697, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3596 (p : Pattern) (guard : d0 p = 1) : d461 p ≤ (2 : Int) + d221 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3597 (p : Pattern) (guard : d4077 p = 1) : d698 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d4077, d698, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3598 (p : Pattern) (guard : d4077 p = 1) : d699 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3597 p hg
    simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d699, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3599 (p : Pattern) (guard : d4077 p = 1) : d700 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3595 p hg
    simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3598 p hg
    simpa only [d700, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3600 (p : Pattern) (guard : d1 p = 1) : d281 p ≤ (2 : Int) + d281 p := by
  omega
theorem compare3601 (p : Pattern) (guard : d0 p = 1) : d471 p ≤ (2 : Int) + d289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3602 (p : Pattern) (guard : d4077 p = 1) : d701 p ≤ (2 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3601 p hg
    simpa only [d4077, d701, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3603 (p : Pattern) (guard : d1 p = 1) : d297 p ≤ (2 : Int) + d297 p := by
  omega
theorem compare3604 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3605 (p : Pattern) (guard : d4077 p = 1) : d702 p ≤ (2 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3603 p hg
    simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3604 p hg
    simpa only [d4077, d702, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3606 (p : Pattern) (guard : d4077 p = 1) : d703 p ≤ (2 : Int) + d306 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3602 p hg
    simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d703, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3607 (p : Pattern) (guard : d4077 p = 1) : d704 p ≤ (2 : Int) + d307 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d704, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3608 (p : Pattern) (guard : d4077 p = 1) : d705 p ≤ (2 : Int) + d308 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3607 p hg
    simpa only [d705, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3609 (p : Pattern) (guard : d4077 p = 1) : d706 p ≤ (2 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3599 p hg
    simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3608 p hg
    simpa only [d706, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3610 (p : Pattern) (guard : d4077 p = 1) : d707 p ≤ (2 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3609 p hg
    simpa only [d707, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3611 (p : Pattern) (guard : d4077 p = 1) : d708 p ≤ (2 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3566 p hg
    simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3610 p hg
    simpa only [d708, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3612 (p : Pattern) (guard : d4077 p = 1) : d709 p ≤ (2 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3590 p hg
    simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3611 p hg
    simpa only [d709, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3613 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d337 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3614 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1151 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3613 p hg
    simpa only [d4148, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3615 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3616 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3615 p hg
    simpa only [d4148, d21, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3617 (p : Pattern) (guard : d4148 p = 1) : d22 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d22, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d22, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d22, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d22, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3618 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3619 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d21, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d4148, d21, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3620 (p : Pattern) (guard : d4148 p = 1) : d27 p ≤ (0 : Int) + d27 p := by
  omega
theorem compare3621 (p : Pattern) (guard : d4148 p = 1) : d28 p ≤ (0 : Int) + d1155 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d28, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3619 p hg
    simpa only [d28, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d28, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d28, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3622 (p : Pattern) (guard : d4148 p = 1) : d29 p ≤ (0 : Int) + d1156 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d29, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d29, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d29, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3621 p hg
    simpa only [d29, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3623 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d33 p := by
  omega
theorem compare3624 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3625 (p : Pattern) (guard : d4148 p = 1) : d38 p ≤ (0 : Int) + d1157 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d38, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d38, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d38, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3624 p hg
    simpa only [d4148, d38, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3626 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d42 p := by
  omega
theorem compare3627 (p : Pattern) (guard : d0 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3628 (p : Pattern) (guard : d4148 p = 1) : d44 p ≤ (0 : Int) + d1158 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d44, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d4148, d44, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d44, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d4148, d44, d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3629 (p : Pattern) (guard : d4148 p = 1) : d45 p ≤ (0 : Int) + d1159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d45, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3625 p hg
    simpa only [d45, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d45, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d45, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3630 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d46 p := by
  omega
theorem compare3631 (p : Pattern) (guard : d4148 p = 1) : d47 p ≤ (0 : Int) + d1160 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d47, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3630 p hg
    simpa only [d4148, d47, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d47, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d4148, d47, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3632 (p : Pattern) (guard : d4148 p = 1) : d49 p ≤ (0 : Int) + d49 p := by
  omega
theorem compare3633 (p : Pattern) (guard : d4148 p = 1) : d50 p ≤ (0 : Int) + d1161 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d50, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3631 p hg
    simpa only [d50, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d50, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3632 p hg
    simpa only [d50, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3634 (p : Pattern) (guard : d4148 p = 1) : d51 p ≤ (0 : Int) + d1162 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d51, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3629 p hg
    simpa only [d51, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d51, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d51, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3635 (p : Pattern) (guard : d4148 p = 1) : d52 p ≤ (0 : Int) + d1163 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d52, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3622 p hg
    simpa only [d52, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d52, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3634 p hg
    simpa only [d52, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3636 (p : Pattern) (guard : d0 p = 1) : d392 p ≤ (0 : Int) + d1175 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3637 (p : Pattern) (guard : d4303 p = 1) : d653 p ≤ (0 : Int) + d1176 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4303, d653, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3635 p hg
    simpa only [d4303, d653, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4303, d653, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3636 p hg
    simpa only [d4303, d653, d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3638 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (0 : Int) + d354 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3639 (p : Pattern) (guard : d4148 p = 1) : d16 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3638 p hg
    simpa only [d4148, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
