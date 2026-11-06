/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare560 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare561 (p : Pattern) (guard : d737 p = 1) : d113 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d113, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d737, d113, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d113, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare560 p hg
    simpa only [d737, d113, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare562 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d71 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare563 (p : Pattern) (guard : d765 p = 1) : d210 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d210, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare561 p hg
    simpa only [d765, d210, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d210, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare562 p hg
    simpa only [d765, d210, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare564 (p : Pattern) (guard : d0 p = 1) : d213 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare565 (p : Pattern) (guard : d737 p = 1) : d214 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d214, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d737, d214, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d214, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare564 p hg
    simpa only [d737, d214, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare566 (p : Pattern) (guard : d765 p = 1) : d215 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d215, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare565 p hg
    simpa only [d765, d215, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d215, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d765, d215, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare567 (p : Pattern) (guard : d765 p = 1) : d216 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d216, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d216, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d216, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare566 p hg
    simpa only [d216, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare568 (p : Pattern) (guard : d737 p = 1) : d67 p ≤ (0 : Int) + d67 p := by
  omega
theorem compare569 (p : Pattern) (guard : d765 p = 1) : d217 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d217, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare568 p hg
    simpa only [d765, d217, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d217, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare562 p hg
    simpa only [d765, d217, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare570 (p : Pattern) (guard : d765 p = 1) : d73 p ≤ (0 : Int) + d73 p := by
  omega
theorem compare571 (p : Pattern) (guard : d765 p = 1) : d218 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d218, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d218, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d218, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d218, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare572 (p : Pattern) (guard : d765 p = 1) : d219 p ≤ (0 : Int) + d74 p := by
  cases selected : p 108 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare571 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare573 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (14 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare574 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (14 : Int) + d7 p := by
  omega
theorem compare575 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (14 : Int) + d0 p := by
  change (2 : Int) ≤ (14 : Int) + 0
  decide
theorem compare576 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (14 : Int) + d2 p := by
  change (4 : Int) ≤ (14 : Int) + 2
  decide
theorem compare577 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (14 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare576 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare578 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (14 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare577 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare579 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (14 : Int) + d55 p := by
  omega
theorem compare580 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (14 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare581 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (14 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare574 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare580 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare582 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (14 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare580 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare583 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (14 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare581 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare584 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (14 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare581 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare585 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (14 : Int) + d12 p := by
  omega
theorem compare586 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (14 : Int) + d1 p := by
  change (3 : Int) ≤ (14 : Int) + 1
  decide
theorem compare587 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (14 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare575 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare586 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare588 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (14 : Int) + d3 p := by
  change (5 : Int) ≤ (14 : Int) + 3
  decide
theorem compare589 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (14 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare576 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare588 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare590 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (14 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare591 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (14 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare592 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (14 : Int) + d60 p := by
  omega
theorem compare593 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (14 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare592 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare594 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (14 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare580 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare593 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare595 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (14 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare585 p hg
    simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare594 p hg
    simpa only [d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare596 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (14 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare597 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (14 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare594 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare598 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (14 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare599 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (14 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare598 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare600 (p : Pattern) (guard : d1 p = 1) : d112 p ≤ (14 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare584 p hg
    simpa only [d112, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare599 p hg
    simpa only [d112, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare601 (p : Pattern) (guard : d736 p = 1) : d113 p ≤ (14 : Int) + d64 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare573 p hg
    simpa only [d736, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare600 p hg
    simpa only [d736, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare602 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (14 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare603 (p : Pattern) (guard : d810 p = 1) : d210 p ≤ (14 : Int) + d811 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d210, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare601 p hg
    simpa only [d810, d210, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d210, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare602 p hg
    simpa only [d810, d210, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare604 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (14 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare605 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (14 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d211, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d211, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare606 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (14 : Int) + d65 p := by
  omega
theorem compare607 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (14 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare598 p hg
    simpa only [d212, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d212, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare608 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (14 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare605 p hg
    simpa only [d213, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare607 p hg
    simpa only [d213, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare609 (p : Pattern) (guard : d736 p = 1) : d214 p ≤ (14 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare604 p hg
    simpa only [d736, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare608 p hg
    simpa only [d736, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare610 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (14 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare611 (p : Pattern) (guard : d810 p = 1) : d215 p ≤ (14 : Int) + d812 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d215, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare609 p hg
    simpa only [d810, d215, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d215, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d810, d215, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare612 (p : Pattern) (guard : d810 p = 1) : d216 p ≤ (14 : Int) + d813 p := by
  cases selected : p 132 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d216, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare603 p hg
    simpa only [d216, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d216, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare611 p hg
    simpa only [d216, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare613 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (14 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d66, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d66, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare614 (p : Pattern) (guard : d736 p = 1) : d67 p ≤ (14 : Int) + d64 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare573 p hg
    simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d736, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare615 (p : Pattern) (guard : d810 p = 1) : d217 p ≤ (14 : Int) + d811 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d217, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare614 p hg
    simpa only [d810, d217, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d217, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare602 p hg
    simpa only [d810, d217, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare616 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (14 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare617 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (14 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare618 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (14 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare616 p hg
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare617 p hg
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare619 (p : Pattern) (guard : d736 p = 1) : d71 p ≤ (14 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare604 p hg
    simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare618 p hg
    simpa only [d736, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare620 (p : Pattern) (guard : d810 p = 1) : d73 p ≤ (14 : Int) + d812 p := by
  cases selected : p 133 with
  | false =>
    have hg : d736 p = 1 := by simpa only [d810, d73, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare619 p hg
    simpa only [d810, d73, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d810, d73, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d810, d73, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare621 (p : Pattern) (guard : d810 p = 1) : d218 p ≤ (14 : Int) + d813 p := by
  cases selected : p 132 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare615 p hg
    simpa only [d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare620 p hg
    simpa only [d218, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare622 (p : Pattern) (guard : d810 p = 1) : d219 p ≤ (14 : Int) + d813 p := by
  cases selected : p 108 with
  | false =>
    have hg : d810 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare612 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d810 p = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare621 p hg
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare623 (p : Pattern) (guard : d753 p = 1) : d210 p ≤ (0 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d210, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d753, d210, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d210, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare278 p hg
    simpa only [d753, d210, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare624 (p : Pattern) (guard : d0 p = 1) : d215 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare625 (p : Pattern) (guard : d754 p = 1) : d216 p ≤ (0 : Int) + d199 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d216, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare623 p hg
    simpa only [d754, d216, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d216, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare624 p hg
    simpa only [d754, d216, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare626 (p : Pattern) (guard : d753 p = 1) : d217 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d217, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare157 p hg
    simpa only [d753, d217, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d217, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d753, d217, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare627 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare628 (p : Pattern) (guard : d754 p = 1) : d218 p ≤ (0 : Int) + d200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d218, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare626 p hg
    simpa only [d754, d218, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d218, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare627 p hg
    simpa only [d754, d218, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare629 (p : Pattern) (guard : d754 p = 1) : d219 p ≤ (0 : Int) + d201 p := by
  cases selected : p 108 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d219, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare625 p hg
    simpa only [d219, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d219, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare628 p hg
    simpa only [d219, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare630 (p : Pattern) (guard : d0 p = 1) : d210 p ≤ (12 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare631 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (12 : Int) + d57 p := by
  omega
theorem compare632 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (12 : Int) + d0 p := by
  change (2 : Int) ≤ (12 : Int) + 0
  decide
theorem compare633 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (12 : Int) + d2 p := by
  change (4 : Int) ≤ (12 : Int) + 2
  decide
theorem compare634 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (12 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare635 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare634 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare636 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d55 p := by
  omega
theorem compare637 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare638 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare639 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (12 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare640 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (12 : Int) + d63 p := by
  omega
theorem compare641 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (12 : Int) + d1 p := by
  change (3 : Int) ≤ (12 : Int) + 1
  decide
theorem compare642 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (12 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare641 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare643 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (12 : Int) + d3 p := by
  change (5 : Int) ≤ (12 : Int) + 3
  decide
theorem compare644 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (12 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare643 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare645 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (12 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare642 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare646 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare642 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare645 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare647 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d65, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare648 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d60 p := by
  omega
theorem compare649 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare650 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare649 p hg
    simpa only [d65, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare651 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare652 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (12 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare653 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (12 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare639 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare652 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare654 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (12 : Int) + d106 p := by
  omega
theorem compare655 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare656 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (12 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare654 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare657 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d107 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare658 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (12 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare656 p hg
    simpa only [d211, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare657 p hg
    simpa only [d211, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare659 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (12 : Int) + d109 p := by
  omega
theorem compare660 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d65 p := by
  omega
theorem compare661 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare662 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (12 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare663 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d110 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare664 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (12 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d212, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d212, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare665 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (12 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d213, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d213, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare666 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (12 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare653 p hg
    simpa only [d214, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d214, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare667 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (12 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare668 (p : Pattern) (guard : d753 p = 1) : d215 p ≤ (12 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d215, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d753, d215, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d215, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d753, d215, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare669 (p : Pattern) (guard : d771 p = 1) : d216 p ≤ (12 : Int) + d134 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare630 p hg
    simpa only [d771, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d753 p = 1 := by simpa only [d771, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d771, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare670 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (12 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare671 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (12 : Int) + d66 p := by
  omega
theorem compare672 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (12 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare653 p hg
    simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare673 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (12 : Int) + d151 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare674 (p : Pattern) (guard : d753 p = 1) : d73 p ≤ (12 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d73, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d753, d73, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d73, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare673 p hg
    simpa only [d753, d73, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare675 (p : Pattern) (guard : d771 p = 1) : d218 p ≤ (12 : Int) + d152 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d771, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d753 p = 1 := by simpa only [d771, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare674 p hg
    simpa only [d771, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare676 (p : Pattern) (guard : d771 p = 1) : d219 p ≤ (12 : Int) + d814 p := by
  cases selected : p 108 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d219, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d219, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d771 p = 1 := by simpa only [d219, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare675 p hg
    simpa only [d219, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare677 (p : Pattern) (guard : d0 p = 1) : d218 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare678 (p : Pattern) (guard : d766 p = 1) : d219 p ≤ (0 : Int) + d75 p := by
  cases selected : p 108 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d766, d219, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d766, d219, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d766, d219, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d766, d219, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare679 (p : Pattern) (guard : d0 p = 1) : d215 p ≤ (0 : Int) + d135 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare680 (p : Pattern) (guard : d754 p = 1) : d216 p ≤ (0 : Int) + d136 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d216, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare623 p hg
    simpa only [d754, d216, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d216, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare679 p hg
    simpa only [d754, d216, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare681 (p : Pattern) (guard : d0 p = 1) : d73 p ≤ (0 : Int) + d159 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare682 (p : Pattern) (guard : d754 p = 1) : d218 p ≤ (0 : Int) + d160 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d218, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare626 p hg
    simpa only [d754, d218, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d218, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d754, d218, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare683 (p : Pattern) (guard : d754 p = 1) : d219 p ≤ (0 : Int) + d161 p := by
  cases selected : p 108 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d219, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d219, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d219, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d219, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare684 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare685 (p : Pattern) (guard : d758 p = 1) : d57 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d758, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare686 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare687 (p : Pattern) (guard : d758 p = 1) : d63 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d758, d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare688 (p : Pattern) (guard : d758 p = 1) : d64 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare689 (p : Pattern) (guard : d818 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare690 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare691 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare692 (p : Pattern) (guard : d818 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d818, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare693 (p : Pattern) (guard : d818 p = 1) : d108 p ≤ (0 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare694 (p : Pattern) (guard : d818 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare695 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare696 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare697 (p : Pattern) (guard : d818 p = 1) : d110 p ≤ (0 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d818, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare698 (p : Pattern) (guard : d818 p = 1) : d111 p ≤ (0 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare699 (p : Pattern) (guard : d818 p = 1) : d112 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d818 p = 1 := by simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d112, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
