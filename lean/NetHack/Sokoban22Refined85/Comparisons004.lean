/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare560 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (1 : Int) + d310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare561 (p : Pattern) (guard : d4040 p = 1) : d483 p ≤ (1 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare560 p hg
    simpa only [d4040, d483, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare562 (p : Pattern) (guard : d4040 p = 1) : d484 p ≤ (1 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare559 p hg
    simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare561 p hg
    simpa only [d484, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare563 (p : Pattern) (guard : d0 p = 1) : d483 p ≤ (0 : Int) + d480 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare564 (p : Pattern) (guard : d4044 p = 1) : d484 p ≤ (0 : Int) + d481 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4044, d484, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d4044, d484, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4044, d484, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare563 p hg
    simpa only [d4044, d484, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare565 (p : Pattern) (guard : d0 p = 1) : d482 p ≤ (1 : Int) + d169 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare566 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (1 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare567 (p : Pattern) (guard : d4040 p = 1) : d483 p ≤ (1 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d483, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4040, d483, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d483, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare566 p hg
    simpa only [d4040, d483, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare568 (p : Pattern) (guard : d4045 p = 1) : d484 p ≤ (1 : Int) + d169 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4045, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare565 p hg
    simpa only [d4045, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d4045, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare567 p hg
    simpa only [d4045, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare569 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d209 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare570 (p : Pattern) (guard : d4042 p = 1) : d101 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare569 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare571 (p : Pattern) (guard : d0 p = 1) : d479 p ≤ (0 : Int) + d265 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare572 (p : Pattern) (guard : d4048 p = 1) : d483 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d483, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d4048, d483, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d483, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare571 p hg
    simpa only [d4048, d483, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare573 (p : Pattern) (guard : d4052 p = 1) : d484 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4052, d484, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare543 p hg
    simpa only [d4052, d484, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d4052, d484, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare572 p hg
    simpa only [d4052, d484, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare574 (p : Pattern) (guard : d0 p = 1) : d311 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare575 (p : Pattern) (guard : d4046 p = 1) : d312 p ≤ (1 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4039 p = 1 := by simpa only [d4046, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare527 p hg
    simpa only [d4046, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4046, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare574 p hg
    simpa only [d4046, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare576 (p : Pattern) (guard : d0 p = 1) : d168 p ≤ (0 : Int) + d485 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare577 (p : Pattern) (guard : d4048 p = 1) : d169 p ≤ (0 : Int) + d485 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare576 p hg
    simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare578 (p : Pattern) (guard : d0 p = 1) : d310 p ≤ (0 : Int) + d486 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare579 (p : Pattern) (guard : d4048 p = 1) : d311 p ≤ (0 : Int) + d487 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d4048, d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare578 p hg
    simpa only [d4048, d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare580 (p : Pattern) (guard : d4048 p = 1) : d312 p ≤ (0 : Int) + d488 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4048 p = 1 := by simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare577 p hg
    simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare579 p hg
    simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare581 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare582 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare581 p hg
    simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare583 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare354 p hg
    simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare582 p hg
    simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare584 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare583 p hg
    simpa only [d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare585 (p : Pattern) (guard : d0 p = 1) : d168 p ≤ (1 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare586 (p : Pattern) (guard : d4040 p = 1) : d169 p ≤ (1 : Int) + d168 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare584 p hg
    simpa only [d4040, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare585 p hg
    simpa only [d4040, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare587 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d12 p := by
  change (9 : Int) ≤ (1 : Int) + 12
  decide
theorem compare588 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare589 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare587 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare588 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare590 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare591 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare592 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d55, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare593 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare592 p hg
    simpa only [d56, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare594 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d61, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare595 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (1 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare594 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d64, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare596 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare593 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare595 p hg
    simpa only [d65, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare597 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare598 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d68, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare599 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare598 p hg
    simpa only [d69, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare600 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d71, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare601 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (1 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare600 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d74, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare602 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare599 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare601 p hg
    simpa only [d75, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare603 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (1 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare602 p hg
    simpa only [d76, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare604 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare603 p hg
    simpa only [d77, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare605 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d86, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare606 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare605 p hg
    simpa only [d87, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare607 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare604 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d88, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare608 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare606 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare352 p hg
    simpa only [d97, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare609 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare607 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare608 p hg
    simpa only [d98, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare610 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d3 p := by
  change (0 : Int) ≤ (1 : Int) + 3
  decide
theorem compare611 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (1 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d13, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare612 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare610 p hg
    simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare611 p hg
    simpa only [d14, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare613 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (1 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare612 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare614 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d33, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d33, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare615 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (1 : Int) + d270 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d37, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d37, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare616 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare614 p hg
    simpa only [d38, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare615 p hg
    simpa only [d38, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare617 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (1 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d42, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d42, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare618 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d7 p := by
  change (4 : Int) ≤ (1 : Int) + 7
  decide
theorem compare619 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare618 p hg
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d17, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare620 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare618 p hg
    simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare619 p hg
    simpa only [d18, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare621 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare620 p hg
    simpa only [d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare622 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare621 p hg
    simpa only [d43, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d43, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare623 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (1 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare617 p hg
    simpa only [d44, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d44, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare624 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare616 p hg
    simpa only [d45, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare623 p hg
    simpa only [d45, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare625 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (1 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d46, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d46, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare626 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (1 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare625 p hg
    simpa only [d47, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d47, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare627 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare589 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare628 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (1 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare627 p hg
    simpa only [d48, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d48, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare629 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (1 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare628 p hg
    simpa only [d49, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d49, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare630 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (1 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare626 p hg
    simpa only [d50, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare629 p hg
    simpa only [d50, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare631 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (1 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare624 p hg
    simpa only [d51, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare630 p hg
    simpa only [d51, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare632 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d52, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d52, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare633 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d5 p := by
  change (2 : Int) ≤ (1 : Int) + 5
  decide
theorem compare634 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d30, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare635 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare633 p hg
    simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare634 p hg
    simpa only [d31, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare636 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare637 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (1 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d66, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d66, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare638 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (1 : Int) + d284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare615 p hg
    simpa only [d67, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare637 p hg
    simpa only [d67, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare639 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d68, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare597 p hg
    simpa only [d68, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare640 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d286 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d69, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare639 p hg
    simpa only [d69, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare641 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare622 p hg
    simpa only [d71, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d71, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare642 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (1 : Int) + d287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare641 p hg
    simpa only [d74, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d74, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare643 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d75, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare642 p hg
    simpa only [d75, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare644 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (1 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare596 p hg
    simpa only [d76, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare643 p hg
    simpa only [d76, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare645 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare632 p hg
    simpa only [d77, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare644 p hg
    simpa only [d77, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare646 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (1 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare612 p hg
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d15, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare647 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare613 p hg
    simpa only [d16, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d16, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare648 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (1 : Int) + d291 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare649 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare620 p hg
    simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d19, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare650 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d292 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare621 p hg
    simpa only [d20, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare649 p hg
    simpa only [d20, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare651 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d293 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d21, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d21, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare652 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d294 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d22, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d22, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare653 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare627 p hg
    simpa only [d26, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare590 p hg
    simpa only [d26, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare654 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (1 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare653 p hg
    simpa only [d27, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d27, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare655 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (1 : Int) + d295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d28, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare654 p hg
    simpa only [d28, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare656 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare652 p hg
    simpa only [d29, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d29, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare657 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (1 : Int) + d297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare656 p hg
    simpa only [d82, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d82, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare658 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d32, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d32, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare659 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d53, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d53, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare660 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d299 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare647 p hg
    simpa only [d54, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d54, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare661 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d55, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare591 p hg
    simpa only [d55, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare662 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d56, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d56, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare663 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare650 p hg
    simpa only [d61, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare108 p hg
    simpa only [d61, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare664 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (1 : Int) + d302 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d64, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d64, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare665 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d303 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d65, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d65, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare666 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d304 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d86, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d86, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare667 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare657 p hg
    simpa only [d87, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare666 p hg
    simpa only [d87, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare668 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d306 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare645 p hg
    simpa only [d88, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d88, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare669 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (1 : Int) + d307 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare667 p hg
    simpa only [d99, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d99, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare670 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (1 : Int) + d308 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d100, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d100, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare671 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d309 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare609 p hg
    simpa only [d101, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d101, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare672 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (1 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare671 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare673 (p : Pattern) (guard : d0 p = 1) : d310 p ≤ (1 : Int) + d310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare674 (p : Pattern) (guard : d4040 p = 1) : d311 p ≤ (1 : Int) + d310 p := by
  cases selected : p 49 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4040, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d4040, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4040, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare673 p hg
    simpa only [d4040, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare675 (p : Pattern) (guard : d4040 p = 1) : d312 p ≤ (1 : Int) + d4053 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d312, d4053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare586 p hg
    simpa only [d312, d4053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4040 p = 1 := by simpa only [d312, d4053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare674 p hg
    simpa only [d312, d4053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare676 (p : Pattern) (guard : d4042 p = 1) : d101 p ≤ (0 : Int) + d101 p := by
  omega
theorem compare677 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) ≤ (0 : Int) + 1
  decide
theorem compare678 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare679 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare680 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare679 p hg
    simpa only [d14, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare681 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare682 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d16, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare683 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  change (4 : Int) ≤ (0 : Int) + 5
  decide
theorem compare684 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare683 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare685 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare683 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d18, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare686 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare687 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d20, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare688 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare689 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare690 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d10 p := by
  change (9 : Int) ≤ (0 : Int) + 10
  decide
theorem compare691 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare692 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare693 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare694 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare693 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare695 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare696 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare697 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare696 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare698 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  change (2 : Int) ≤ (0 : Int) + 3
  decide
theorem compare699 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
