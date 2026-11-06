/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare560 (p : Pattern) (guard : d0 p = 1) : d94 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare561 (p : Pattern) (guard : d841 p = 1) : d95 p ≤ (0 : Int) + d267 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d95, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d95, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d95, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare560 p hg
    simpa only [d841, d95, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare562 (p : Pattern) (guard : d841 p = 1) : d96 p ≤ (0 : Int) + d268 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d96, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d96, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d96, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare561 p hg
    simpa only [d96, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare563 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (0 : Int) + d100 p := by
  omega
theorem compare564 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare565 (p : Pattern) (guard : d841 p = 1) : d102 p ≤ (0 : Int) + d269 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d102, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d102, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d102, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare564 p hg
    simpa only [d841, d102, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare566 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare567 (p : Pattern) (guard : d841 p = 1) : d102 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d102, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d102, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d102, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare566 p hg
    simpa only [d841, d102, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare568 (p : Pattern) (guard : d841 p = 1) : d102 p ≤ (0 : Int) + d271 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare565 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare569 (p : Pattern) (guard : d841 p = 1) : d103 p ≤ (0 : Int) + d272 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d103, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare562 p hg
    simpa only [d103, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d103, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare568 p hg
    simpa only [d103, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare570 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare571 (p : Pattern) (guard : d841 p = 1) : d105 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d105, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d105, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d105, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d841, d105, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare572 (p : Pattern) (guard : d841 p = 1) : d106 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d106, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d106, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d106, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare571 p hg
    simpa only [d106, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare573 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare574 (p : Pattern) (guard : d841 p = 1) : d108 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d108, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d841, d108, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d108, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare573 p hg
    simpa only [d841, d108, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare575 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d110 p := by
  omega
theorem compare576 (p : Pattern) (guard : d0 p = 1) : d111 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare577 (p : Pattern) (guard : d841 p = 1) : d112 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d112, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d841, d112, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d112, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare576 p hg
    simpa only [d841, d112, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare578 (p : Pattern) (guard : d841 p = 1) : d113 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d113, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare574 p hg
    simpa only [d113, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d113, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare577 p hg
    simpa only [d113, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare579 (p : Pattern) (guard : d841 p = 1) : d114 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d114, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare572 p hg
    simpa only [d114, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d114, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d114, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare580 (p : Pattern) (guard : d841 p = 1) : d115 p ≤ (0 : Int) + d278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d115, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d115, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d115, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d115, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare581 (p : Pattern) (guard : d841 p = 1) : d116 p ≤ (0 : Int) + d279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d116, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare558 p hg
    simpa only [d116, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d116, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare580 p hg
    simpa only [d116, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare582 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare583 (p : Pattern) (guard : d841 p = 1) : d45 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d45, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d45, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d45, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d841, d45, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare584 (p : Pattern) (guard : d841 p = 1) : d45 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare538 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare585 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare586 (p : Pattern) (guard : d841 p = 1) : d65 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d65, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d65, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d65, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare585 p hg
    simpa only [d841, d65, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare587 (p : Pattern) (guard : d841 p = 1) : d66 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d66, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare541 p hg
    simpa only [d66, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d66, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare586 p hg
    simpa only [d66, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare588 (p : Pattern) (guard : d841 p = 1) : d67 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d67, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare584 p hg
    simpa only [d67, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d67, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d67, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare589 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare590 (p : Pattern) (guard : d841 p = 1) : d77 p ≤ (0 : Int) + d280 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d77, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d841, d77, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d77, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d841, d77, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare591 (p : Pattern) (guard : d841 p = 1) : d77 p ≤ (0 : Int) + d281 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare550 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare592 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare593 (p : Pattern) (guard : d841 p = 1) : d80 p ≤ (0 : Int) + d282 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d80, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d841, d80, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d80, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare592 p hg
    simpa only [d841, d80, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare594 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare595 (p : Pattern) (guard : d841 p = 1) : d82 p ≤ (0 : Int) + d283 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d82, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare542 p hg
    simpa only [d841, d82, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d82, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare594 p hg
    simpa only [d841, d82, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare596 (p : Pattern) (guard : d841 p = 1) : d83 p ≤ (0 : Int) + d284 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d83, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare593 p hg
    simpa only [d83, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d83, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d83, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare597 (p : Pattern) (guard : d841 p = 1) : d117 p ≤ (0 : Int) + d285 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d117, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d117, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d117, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d117, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare598 (p : Pattern) (guard : d841 p = 1) : d118 p ≤ (0 : Int) + d286 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d118, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare588 p hg
    simpa only [d118, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d118, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d118, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare599 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare600 (p : Pattern) (guard : d841 p = 1) : d123 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d123, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d841, d123, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d123, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare599 p hg
    simpa only [d841, d123, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare601 (p : Pattern) (guard : d841 p = 1) : d124 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d124, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d124, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d124, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare600 p hg
    simpa only [d124, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare602 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare603 (p : Pattern) (guard : d841 p = 1) : d126 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d841, d126, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d841, d126, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d841, d126, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare602 p hg
    simpa only [d841, d126, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare604 (p : Pattern) (guard : d841 p = 1) : d127 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d127, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d127, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d127, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare603 p hg
    simpa only [d127, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare605 (p : Pattern) (guard : d841 p = 1) : d128 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d128, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare601 p hg
    simpa only [d128, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d128, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare604 p hg
    simpa only [d128, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare606 (p : Pattern) (guard : d841 p = 1) : d129 p ≤ (0 : Int) + d287 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d129, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d129, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d129, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d129, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare607 (p : Pattern) (guard : d841 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare608 (p : Pattern) (guard : d841 p = 1) : d130 p ≤ (0 : Int) + d288 p := by
  cases selected : p 113 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d130, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare577 p hg
    simpa only [d130, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d130, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare607 p hg
    simpa only [d130, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare609 (p : Pattern) (guard : d841 p = 1) : d131 p ≤ (0 : Int) + d289 p := by
  cases selected : p 112 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d131, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d131, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d131, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare608 p hg
    simpa only [d131, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare610 (p : Pattern) (guard : d841 p = 1) : d132 p ≤ (0 : Int) + d290 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d132, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare605 p hg
    simpa only [d132, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d132, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare609 p hg
    simpa only [d132, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare611 (p : Pattern) (guard : d841 p = 1) : d133 p ≤ (0 : Int) + d291 p := by
  cases selected : p 86 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d133, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare598 p hg
    simpa only [d133, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d133, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d133, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare612 (p : Pattern) (guard : d841 p = 1) : d134 p ≤ (0 : Int) + d292 p := by
  cases selected : p 80 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d134, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare581 p hg
    simpa only [d134, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d134, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare611 p hg
    simpa only [d134, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare613 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare614 (p : Pattern) (guard : d829 p = 1) : d177 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d177, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d829, d177, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d177, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d829, d177, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare615 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare616 (p : Pattern) (guard : d829 p = 1) : d178 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d178, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d829, d178, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d178, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare615 p hg
    simpa only [d829, d178, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare617 (p : Pattern) (guard : d829 p = 1) : d179 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d179, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare614 p hg
    simpa only [d179, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d179, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare616 p hg
    simpa only [d179, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare618 (p : Pattern) (guard : d0 p = 1) : d182 p ≤ (0 : Int) + d172 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare619 (p : Pattern) (guard : d838 p = 1) : d183 p ≤ (0 : Int) + d173 p := by
  cases selected : p 80 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d838, d183, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare617 p hg
    simpa only [d838, d183, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d838, d183, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare618 p hg
    simpa only [d838, d183, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare620 (p : Pattern) (guard : d0 p = 1) : d179 p ≤ (1 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare621 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (1 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare622 (p : Pattern) (guard : d829 p = 1) : d180 p ≤ (1 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d180, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1 p hg
    simpa only [d829, d180, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d180, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare621 p hg
    simpa only [d829, d180, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare623 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare624 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare623 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare625 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare624 p hg
    simpa only [d18, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare626 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare624 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare627 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare625 p hg
    simpa only [d20, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare626 p hg
    simpa only [d20, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare628 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (1 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare627 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare629 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (1 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare628 p hg
    simpa only [d120, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44 p hg
    simpa only [d120, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare630 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (1 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34 p hg
    simpa only [d121, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare629 p hg
    simpa only [d121, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare631 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (1 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare630 p hg
    simpa only [d122, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47 p hg
    simpa only [d122, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare632 (p : Pattern) (guard : d1 p = 1) : d123 p ≤ (1 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d123, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33 p hg
    simpa only [d123, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d123, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d123, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare633 (p : Pattern) (guard : d1 p = 1) : d124 p ≤ (1 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d124, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32 p hg
    simpa only [d124, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d124, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d124, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare634 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (1 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare635 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (1 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d110, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare634 p hg
    simpa only [d110, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare636 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare637 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare638 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare639 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (1 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare634 p hg
    simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare640 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (1 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d126, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare639 p hg
    simpa only [d126, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare641 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (1 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare51 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare642 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (1 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d128, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare641 p hg
    simpa only [d128, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare643 (p : Pattern) (guard : d0 p = 1) : d170 p ≤ (1 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare644 (p : Pattern) (guard : d829 p = 1) : d181 p ≤ (1 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d181, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare642 p hg
    simpa only [d829, d181, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d181, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare643 p hg
    simpa only [d829, d181, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare645 (p : Pattern) (guard : d829 p = 1) : d182 p ≤ (1 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d182, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d182, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d182, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d182, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare646 (p : Pattern) (guard : d830 p = 1) : d183 p ≤ (1 : Int) + d116 p := by
  cases selected : p 80 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d830, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare620 p hg
    simpa only [d830, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d830, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare645 p hg
    simpa only [d830, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare647 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d265 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare648 (p : Pattern) (guard : d870 p = 1) : d177 p ≤ (0 : Int) + d266 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d177, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare546 p hg
    simpa only [d870, d177, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d177, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d870, d177, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare649 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare650 (p : Pattern) (guard : d870 p = 1) : d178 p ≤ (0 : Int) + d278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d178, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d870, d178, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d178, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare649 p hg
    simpa only [d870, d178, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare651 (p : Pattern) (guard : d870 p = 1) : d179 p ≤ (0 : Int) + d279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d179, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d179, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d179, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d179, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare652 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d285 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare653 (p : Pattern) (guard : d870 p = 1) : d180 p ≤ (0 : Int) + d286 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d180, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare588 p hg
    simpa only [d870, d180, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d180, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare652 p hg
    simpa only [d870, d180, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare654 (p : Pattern) (guard : d0 p = 1) : d170 p ≤ (0 : Int) + d289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare655 (p : Pattern) (guard : d870 p = 1) : d181 p ≤ (0 : Int) + d290 p := by
  cases selected : p 106 with
  | false =>
    have hg : d841 p = 1 := by simpa only [d870, d181, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare605 p hg
    simpa only [d870, d181, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d870, d181, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare654 p hg
    simpa only [d870, d181, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare656 (p : Pattern) (guard : d870 p = 1) : d182 p ≤ (0 : Int) + d291 p := by
  cases selected : p 86 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d182, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare653 p hg
    simpa only [d182, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d182, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d182, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare657 (p : Pattern) (guard : d870 p = 1) : d183 p ≤ (0 : Int) + d292 p := by
  cases selected : p 80 with
  | false =>
    have hg : d870 p = 1 := by simpa only [d183, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d183, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d870 p = 1 := by simpa only [d183, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare656 p hg
    simpa only [d183, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare658 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d879 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare659 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare660 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare661 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare662 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare663 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare664 (p : Pattern) (guard : d873 p = 1) : d8 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d873, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d873, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare665 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  omega
theorem compare666 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare667 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare668 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare669 (p : Pattern) (guard : d873 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d873, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d873, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare670 (p : Pattern) (guard : d873 p = 1) : d15 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare671 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare672 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare673 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare674 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare673 p hg
    simpa only [d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare675 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare676 (p : Pattern) (guard : d873 p = 1) : d33 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare674 p hg
    simpa only [d873, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare675 p hg
    simpa only [d873, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare677 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare678 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare679 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d22, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare680 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare681 (p : Pattern) (guard : d873 p = 1) : d24 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare679 p hg
    simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare682 (p : Pattern) (guard : d873 p = 1) : d34 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d34, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d34, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d34, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d34, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare683 (p : Pattern) (guard : d873 p = 1) : d35 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d35, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d35, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d35, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d35, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare684 (p : Pattern) (guard : d873 p = 1) : d36 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare683 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare685 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare686 (p : Pattern) (guard : d873 p = 1) : d38 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d873, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d873, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare687 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare688 (p : Pattern) (guard : d873 p = 1) : d40 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d873, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d873, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare689 (p : Pattern) (guard : d873 p = 1) : d41 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare690 (p : Pattern) (guard : d873 p = 1) : d42 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare691 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare692 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare693 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d4, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare694 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare695 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d18, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare696 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare697 (p : Pattern) (guard : d873 p = 1) : d20 p ≤ (0 : Int) + d19 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare698 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare699 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
