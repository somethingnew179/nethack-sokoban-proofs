/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons203
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28560 (p : Pattern) (guard : d5268 p = 1) : d3375 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3375, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28561 (p : Pattern) (guard : d5268 p = 1) : d3376 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28560 p hg
    simpa only [d3376, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28562 (p : Pattern) (guard : d5268 p = 1) : d3378 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3378, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28563 (p : Pattern) (guard : d5268 p = 1) : d3379 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28562 p hg
    simpa only [d3379, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28564 (p : Pattern) (guard : d5268 p = 1) : d3380 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28561 p hg
    simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28563 p hg
    simpa only [d3380, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28565 (p : Pattern) (guard : d5268 p = 1) : d3381 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3381, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28566 (p : Pattern) (guard : d5268 p = 1) : d3382 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3382, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28567 (p : Pattern) (guard : d5268 p = 1) : d3383 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28565 p hg
    simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d3383, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28568 (p : Pattern) (guard : d5268 p = 1) : d3384 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28564 p hg
    simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28567 p hg
    simpa only [d3384, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28569 (p : Pattern) (guard : d5268 p = 1) : d3385 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28483 p hg
    simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3385, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28570 (p : Pattern) (guard : d5268 p = 1) : d3386 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28567 p hg
    simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28569 p hg
    simpa only [d3386, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28571 (p : Pattern) (guard : d5268 p = 1) : d3387 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28568 p hg
    simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28570 p hg
    simpa only [d3387, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28572 (p : Pattern) (guard : d5268 p = 1) : d3388 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28559 p hg
    simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28571 p hg
    simpa only [d3388, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28573 (p : Pattern) (guard : d5268 p = 1) : d3391 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26816 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28574 (p : Pattern) (guard : d5268 p = 1) : d3392 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28573 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d3392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28575 (p : Pattern) (guard : d5268 p = 1) : d3393 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28574 p hg
    simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28549 p hg
    simpa only [d3393, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28576 (p : Pattern) (guard : d5268 p = 1) : d3394 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28560 p hg
    simpa only [d3394, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28577 (p : Pattern) (guard : d5268 p = 1) : d3395 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28575 p hg
    simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3395, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28578 (p : Pattern) (guard : d5268 p = 1) : d3396 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28473 p hg
    simpa only [d3396, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28579 (p : Pattern) (guard : d5268 p = 1) : d3397 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28577 p hg
    simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28578 p hg
    simpa only [d3397, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28580 (p : Pattern) (guard : d5268 p = 1) : d3398 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3398, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28581 (p : Pattern) (guard : d5268 p = 1) : d3399 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28580 p hg
    simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3399, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28582 (p : Pattern) (guard : d5268 p = 1) : d3400 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28579 p hg
    simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28581 p hg
    simpa only [d3400, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28583 (p : Pattern) (guard : d5268 p = 1) : d3401 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3401, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28584 (p : Pattern) (guard : d5268 p = 1) : d3402 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28563 p hg
    simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28583 p hg
    simpa only [d3402, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28585 (p : Pattern) (guard : d5268 p = 1) : d3403 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28483 p hg
    simpa only [d3403, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28586 (p : Pattern) (guard : d5268 p = 1) : d3404 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28584 p hg
    simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28585 p hg
    simpa only [d3404, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28587 (p : Pattern) (guard : d5268 p = 1) : d3405 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28485 p hg
    simpa only [d3405, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28588 (p : Pattern) (guard : d5268 p = 1) : d3406 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28587 p hg
    simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3406, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28589 (p : Pattern) (guard : d5268 p = 1) : d3407 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28586 p hg
    simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28588 p hg
    simpa only [d3407, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28590 (p : Pattern) (guard : d5268 p = 1) : d3408 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28582 p hg
    simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28589 p hg
    simpa only [d3408, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28591 (p : Pattern) (guard : d5268 p = 1) : d3409 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28572 p hg
    simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28590 p hg
    simpa only [d3409, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28592 (p : Pattern) (guard : d5268 p = 1) : d3410 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28555 p hg
    simpa only [d3410, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28593 (p : Pattern) (guard : d5268 p = 1) : d3411 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28592 p hg
    simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28558 p hg
    simpa only [d3411, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28594 (p : Pattern) (guard : d5268 p = 1) : d3412 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28562 p hg
    simpa only [d3412, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28595 (p : Pattern) (guard : d5268 p = 1) : d3413 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28594 p hg
    simpa only [d3413, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28596 (p : Pattern) (guard : d5268 p = 1) : d3414 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28595 p hg
    simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3414, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28597 (p : Pattern) (guard : d5268 p = 1) : d3415 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28596 p hg
    simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3415, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28598 (p : Pattern) (guard : d5268 p = 1) : d3416 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28593 p hg
    simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28597 p hg
    simpa only [d3416, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28599 (p : Pattern) (guard : d5268 p = 1) : d3417 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3417, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28600 (p : Pattern) (guard : d5268 p = 1) : d3418 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28599 p hg
    simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28578 p hg
    simpa only [d3418, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28601 (p : Pattern) (guard : d5268 p = 1) : d3419 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28600 p hg
    simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28581 p hg
    simpa only [d3419, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28602 (p : Pattern) (guard : d5268 p = 1) : d3420 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28594 p hg
    simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3420, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28603 (p : Pattern) (guard : d5268 p = 1) : d3421 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28602 p hg
    simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3421, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28604 (p : Pattern) (guard : d5268 p = 1) : d3422 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28603 p hg
    simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3422, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28605 (p : Pattern) (guard : d5268 p = 1) : d3423 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28601 p hg
    simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28604 p hg
    simpa only [d3423, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28606 (p : Pattern) (guard : d5268 p = 1) : d3424 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28598 p hg
    simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28605 p hg
    simpa only [d3424, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28607 (p : Pattern) (guard : d5268 p = 1) : d3425 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28591 p hg
    simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28606 p hg
    simpa only [d3425, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28608 (p : Pattern) (guard : d5268 p = 1) : d3426 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28557 p hg
    simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3426, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28609 (p : Pattern) (guard : d5268 p = 1) : d3427 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28608 p hg
    simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3427, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28610 (p : Pattern) (guard : d5268 p = 1) : d3428 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28609 p hg
    simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3428, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28611 (p : Pattern) (guard : d5268 p = 1) : d3429 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28610 p hg
    simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3429, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28612 (p : Pattern) (guard : d5268 p = 1) : d3430 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28606 p hg
    simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28611 p hg
    simpa only [d3430, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28613 (p : Pattern) (guard : d5268 p = 1) : d3431 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28607 p hg
    simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28612 p hg
    simpa only [d3431, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28614 (p : Pattern) (guard : d5268 p = 1) : d3432 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28593 p hg
    simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28571 p hg
    simpa only [d3432, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28615 (p : Pattern) (guard : d5268 p = 1) : d3433 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28601 p hg
    simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28589 p hg
    simpa only [d3433, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28616 (p : Pattern) (guard : d5268 p = 1) : d3434 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28614 p hg
    simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28615 p hg
    simpa only [d3434, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28617 (p : Pattern) (guard : d5268 p = 1) : d3435 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28616 p hg
    simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28606 p hg
    simpa only [d3435, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28618 (p : Pattern) (guard : d5268 p = 1) : d3436 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28606 p hg
    simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3436, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28619 (p : Pattern) (guard : d5268 p = 1) : d3437 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28617 p hg
    simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28618 p hg
    simpa only [d3437, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28620 (p : Pattern) (guard : d5268 p = 1) : d3438 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28613 p hg
    simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28619 p hg
    simpa only [d3438, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28621 (p : Pattern) (guard : d5268 p = 1) : d3439 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28526 p hg
    simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28620 p hg
    simpa only [d3439, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28622 (p : Pattern) (guard : d5268 p = 1) : d3440 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28546 p hg
    simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28621 p hg
    simpa only [d3440, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28623 (p : Pattern) (guard : d5268 p = 1) : d3441 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28450 p hg
    simpa only [d3441, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28624 (p : Pattern) (guard : d5268 p = 1) : d3442 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28623 p hg
    simpa only [d3442, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28625 (p : Pattern) (guard : d5268 p = 1) : d3443 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26643 p hg
    simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28453 p hg
    simpa only [d3443, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28626 (p : Pattern) (guard : d5268 p = 1) : d3444 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26648 p hg
    simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3444, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28627 (p : Pattern) (guard : d5268 p = 1) : d3445 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28625 p hg
    simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28626 p hg
    simpa only [d3445, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28628 (p : Pattern) (guard : d5268 p = 1) : d3446 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28624 p hg
    simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28627 p hg
    simpa only [d3446, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28629 (p : Pattern) (guard : d5268 p = 1) : d3447 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28479 p hg
    simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28626 p hg
    simpa only [d3447, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28630 (p : Pattern) (guard : d5268 p = 1) : d3448 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28629 p hg
    simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28486 p hg
    simpa only [d3448, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28631 (p : Pattern) (guard : d5268 p = 1) : d3449 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28628 p hg
    simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28630 p hg
    simpa only [d3449, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28632 (p : Pattern) (guard : d5268 p = 1) : d3450 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28492 p hg
    simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28631 p hg
    simpa only [d3450, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28633 (p : Pattern) (guard : d5268 p = 1) : d3451 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28623 p hg
    simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d3451, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28634 (p : Pattern) (guard : d5268 p = 1) : d3452 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28626 p hg
    simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28485 p hg
    simpa only [d3452, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28635 (p : Pattern) (guard : d5268 p = 1) : d3453 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28633 p hg
    simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28634 p hg
    simpa only [d3453, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28636 (p : Pattern) (guard : d5268 p = 1) : d3454 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28626 p hg
    simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3454, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28637 (p : Pattern) (guard : d5268 p = 1) : d3455 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28636 p hg
    simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3455, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28638 (p : Pattern) (guard : d5268 p = 1) : d3456 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28635 p hg
    simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28637 p hg
    simpa only [d3456, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28639 (p : Pattern) (guard : d5268 p = 1) : d3457 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28500 p hg
    simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28638 p hg
    simpa only [d3457, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28640 (p : Pattern) (guard : d5268 p = 1) : d3458 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28632 p hg
    simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28639 p hg
    simpa only [d3458, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28641 (p : Pattern) (guard : d5268 p = 1) : d3459 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28494 p hg
    simpa only [d3459, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28642 (p : Pattern) (guard : d5268 p = 1) : d3460 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28641 p hg
    simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28495 p hg
    simpa only [d3460, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28643 (p : Pattern) (guard : d5268 p = 1) : d3462 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3462, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28644 (p : Pattern) (guard : d5268 p = 1) : d3463 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28643 p hg
    simpa only [d3463, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28645 (p : Pattern) (guard : d5268 p = 1) : d3464 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28644 p hg
    simpa only [d3464, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28646 (p : Pattern) (guard : d5268 p = 1) : d3465 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28645 p hg
    simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3465, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28647 (p : Pattern) (guard : d5268 p = 1) : d3466 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28646 p hg
    simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3466, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28648 (p : Pattern) (guard : d5268 p = 1) : d3467 p ≤ (0 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28642 p hg
    simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28647 p hg
    simpa only [d3467, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28649 (p : Pattern) (guard : d5268 p = 1) : d3468 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3468, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28650 (p : Pattern) (guard : d5268 p = 1) : d3469 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28649 p hg
    simpa only [d3469, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28651 (p : Pattern) (guard : d5268 p = 1) : d3470 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28650 p hg
    simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28502 p hg
    simpa only [d3470, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28652 (p : Pattern) (guard : d5268 p = 1) : d3471 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28644 p hg
    simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3471, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28653 (p : Pattern) (guard : d5268 p = 1) : d3472 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28652 p hg
    simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3472, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28654 (p : Pattern) (guard : d5268 p = 1) : d3473 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28653 p hg
    simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3473, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28655 (p : Pattern) (guard : d5268 p = 1) : d3474 p ≤ (0 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28651 p hg
    simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28654 p hg
    simpa only [d3474, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28656 (p : Pattern) (guard : d5268 p = 1) : d3475 p ≤ (0 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28648 p hg
    simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28655 p hg
    simpa only [d3475, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28657 (p : Pattern) (guard : d5268 p = 1) : d3476 p ≤ (0 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28640 p hg
    simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28656 p hg
    simpa only [d3476, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28658 (p : Pattern) (guard : d5268 p = 1) : d3477 p ≤ (0 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28656 p hg
    simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3477, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28659 (p : Pattern) (guard : d5268 p = 1) : d3478 p ≤ (0 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28657 p hg
    simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28658 p hg
    simpa only [d3478, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28660 (p : Pattern) (guard : d5268 p = 1) : d3479 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28540 p hg
    simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28659 p hg
    simpa only [d3479, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28661 (p : Pattern) (guard : d5268 p = 1) : d3480 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28526 p hg
    simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28660 p hg
    simpa only [d3480, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28662 (p : Pattern) (guard : d5268 p = 1) : d3481 p ≤ (0 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3481, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28663 (p : Pattern) (guard : d5268 p = 1) : d3482 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28577 p hg
    simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28662 p hg
    simpa only [d3482, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28664 (p : Pattern) (guard : d5268 p = 1) : d3483 p ≤ (0 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28662 p hg
    simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3483, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28665 (p : Pattern) (guard : d5268 p = 1) : d3484 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28663 p hg
    simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28664 p hg
    simpa only [d3484, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28666 (p : Pattern) (guard : d5268 p = 1) : d3485 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3485, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28667 (p : Pattern) (guard : d5268 p = 1) : d3486 p ≤ (0 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28584 p hg
    simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28666 p hg
    simpa only [d3486, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28668 (p : Pattern) (guard : d5268 p = 1) : d3487 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28666 p hg
    simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3487, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28669 (p : Pattern) (guard : d5268 p = 1) : d3488 p ≤ (0 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28667 p hg
    simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28668 p hg
    simpa only [d3488, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28670 (p : Pattern) (guard : d5268 p = 1) : d3489 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28665 p hg
    simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28669 p hg
    simpa only [d3489, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28671 (p : Pattern) (guard : d5268 p = 1) : d3490 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28572 p hg
    simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28670 p hg
    simpa only [d3490, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28672 (p : Pattern) (guard : d5268 p = 1) : d3491 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28599 p hg
    simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28662 p hg
    simpa only [d3491, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28673 (p : Pattern) (guard : d5268 p = 1) : d3492 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28672 p hg
    simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28664 p hg
    simpa only [d3492, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28674 (p : Pattern) (guard : d5268 p = 1) : d3493 p ≤ (0 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28673 p hg
    simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28604 p hg
    simpa only [d3493, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28675 (p : Pattern) (guard : d5268 p = 1) : d3494 p ≤ (0 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28598 p hg
    simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28674 p hg
    simpa only [d3494, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28676 (p : Pattern) (guard : d5268 p = 1) : d3495 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28671 p hg
    simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28675 p hg
    simpa only [d3495, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28677 (p : Pattern) (guard : d5268 p = 1) : d3496 p ≤ (0 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28675 p hg
    simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28611 p hg
    simpa only [d3496, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28678 (p : Pattern) (guard : d5268 p = 1) : d3497 p ≤ (0 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28676 p hg
    simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28677 p hg
    simpa only [d3497, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28679 (p : Pattern) (guard : d5268 p = 1) : d3498 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28562 p hg
    simpa only [d3498, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28680 (p : Pattern) (guard : d5268 p = 1) : d3499 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28679 p hg
    simpa only [d3499, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28681 (p : Pattern) (guard : d5268 p = 1) : d3500 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28680 p hg
    simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28666 p hg
    simpa only [d3500, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28682 (p : Pattern) (guard : d5268 p = 1) : d3501 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3501, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28683 (p : Pattern) (guard : d5268 p = 1) : d3502 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28682 p hg
    simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3502, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28684 (p : Pattern) (guard : d5268 p = 1) : d3503 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28683 p hg
    simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3503, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28685 (p : Pattern) (guard : d5268 p = 1) : d3504 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28681 p hg
    simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28684 p hg
    simpa only [d3504, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28686 (p : Pattern) (guard : d5268 p = 1) : d3505 p ≤ (0 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28593 p hg
    simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28685 p hg
    simpa only [d3505, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28687 (p : Pattern) (guard : d5268 p = 1) : d3506 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28562 p hg
    simpa only [d3506, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28688 (p : Pattern) (guard : d5268 p = 1) : d3507 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28687 p hg
    simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d3507, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28689 (p : Pattern) (guard : d5268 p = 1) : d3508 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28688 p hg
    simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28683 p hg
    simpa only [d3508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28690 (p : Pattern) (guard : d5268 p = 1) : d3509 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28461 p hg
    simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17649 p hg
    simpa only [d3509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28691 (p : Pattern) (guard : d5268 p = 1) : d3510 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28689 p hg
    simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28690 p hg
    simpa only [d3510, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28692 (p : Pattern) (guard : d5268 p = 1) : d3511 p ≤ (0 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28673 p hg
    simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28691 p hg
    simpa only [d3511, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28693 (p : Pattern) (guard : d5268 p = 1) : d3512 p ≤ (0 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28686 p hg
    simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28692 p hg
    simpa only [d3512, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28694 (p : Pattern) (guard : d5268 p = 1) : d3513 p ≤ (0 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d3513, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28695 (p : Pattern) (guard : d5268 p = 1) : d3514 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28694 p hg
    simpa only [d3514, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28696 (p : Pattern) (guard : d5268 p = 1) : d3515 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28695 p hg
    simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28581 p hg
    simpa only [d3515, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28697 (p : Pattern) (guard : d5268 p = 1) : d3516 p ≤ (0 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28696 p hg
    simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28604 p hg
    simpa only [d3516, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28698 (p : Pattern) (guard : d5268 p = 1) : d3517 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28662 p hg
    simpa only [d3517, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28699 (p : Pattern) (guard : d5268 p = 1) : d3518 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28698 p hg
    simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28603 p hg
    simpa only [d3518, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
