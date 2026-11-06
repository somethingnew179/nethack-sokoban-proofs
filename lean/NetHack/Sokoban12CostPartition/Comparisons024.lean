/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3360 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (0 : Int) + d604 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3361 (p : Pattern) (guard : d1134 p = 1) : d382 p ≤ (0 : Int) + d605 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d382, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d1134, d382, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d382, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3360 p hg
    simpa only [d1134, d382, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3362 (p : Pattern) (guard : d1134 p = 1) : d383 p ≤ (0 : Int) + d606 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d383, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3361 p hg
    simpa only [d383, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d383, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d383, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3363 (p : Pattern) (guard : d1134 p = 1) : d384 p ≤ (0 : Int) + d607 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d384, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3359 p hg
    simpa only [d384, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d384, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3362 p hg
    simpa only [d384, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3364 (p : Pattern) (guard : d1134 p = 1) : d385 p ≤ (0 : Int) + d608 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d385, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3359 p hg
    simpa only [d385, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d385, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3363 p hg
    simpa only [d385, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3365 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d594 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3366 (p : Pattern) (guard : d1134 p = 1) : d386 p ≤ (0 : Int) + d609 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d386, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d1134, d386, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d386, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3365 p hg
    simpa only [d1134, d386, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3367 (p : Pattern) (guard : d1134 p = 1) : d387 p ≤ (0 : Int) + d610 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d387, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d387, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d387, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d387, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3368 (p : Pattern) (guard : d0 p = 1) : d274 p ≤ (0 : Int) + d612 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3369 (p : Pattern) (guard : d1134 p = 1) : d388 p ≤ (0 : Int) + d613 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d388, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d1134, d388, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d388, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3368 p hg
    simpa only [d1134, d388, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3370 (p : Pattern) (guard : d1134 p = 1) : d389 p ≤ (0 : Int) + d614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d389, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d389, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d389, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d389, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3371 (p : Pattern) (guard : d1134 p = 1) : d390 p ≤ (0 : Int) + d615 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d390, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3367 p hg
    simpa only [d390, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d390, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3370 p hg
    simpa only [d390, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3372 (p : Pattern) (guard : d1134 p = 1) : d391 p ≤ (0 : Int) + d616 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d391, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3367 p hg
    simpa only [d391, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d391, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3371 p hg
    simpa only [d391, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3373 (p : Pattern) (guard : d1134 p = 1) : d392 p ≤ (0 : Int) + d617 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d392, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3364 p hg
    simpa only [d392, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d392, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3372 p hg
    simpa only [d392, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3374 (p : Pattern) (guard : d1134 p = 1) : d393 p ≤ (0 : Int) + d618 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d393, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3356 p hg
    simpa only [d393, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d393, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3373 p hg
    simpa only [d393, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3375 (p : Pattern) (guard : d1134 p = 1) : d394 p ≤ (0 : Int) + d619 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d394, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d394, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d394, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d394, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3376 (p : Pattern) (guard : d1134 p = 1) : d395 p ≤ (0 : Int) + d620 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d395, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d395, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d395, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d395, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3377 (p : Pattern) (guard : d1134 p = 1) : d396 p ≤ (0 : Int) + d621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d396, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3375 p hg
    simpa only [d396, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d396, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3376 p hg
    simpa only [d396, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3378 (p : Pattern) (guard : d1134 p = 1) : d397 p ≤ (0 : Int) + d622 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d397, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3363 p hg
    simpa only [d397, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d397, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d397, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3379 (p : Pattern) (guard : d1134 p = 1) : d398 p ≤ (0 : Int) + d623 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d398, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3371 p hg
    simpa only [d398, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d398, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d398, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3380 (p : Pattern) (guard : d1134 p = 1) : d399 p ≤ (0 : Int) + d624 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d399, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3378 p hg
    simpa only [d399, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d399, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3379 p hg
    simpa only [d399, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3381 (p : Pattern) (guard : d1134 p = 1) : d400 p ≤ (0 : Int) + d625 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d400, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3377 p hg
    simpa only [d400, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d400, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3380 p hg
    simpa only [d400, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3382 (p : Pattern) (guard : d1134 p = 1) : d401 p ≤ (0 : Int) + d626 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d401, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3374 p hg
    simpa only [d401, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d401, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3381 p hg
    simpa only [d401, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3383 (p : Pattern) (guard : d1134 p = 1) : d402 p ≤ (0 : Int) + d627 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d402, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d402, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d402, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d402, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3384 (p : Pattern) (guard : d1134 p = 1) : d403 p ≤ (0 : Int) + d628 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d403, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3381 p hg
    simpa only [d403, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d403, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d403, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3385 (p : Pattern) (guard : d1134 p = 1) : d404 p ≤ (0 : Int) + d629 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d404, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3382 p hg
    simpa only [d404, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d404, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3384 p hg
    simpa only [d404, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3386 (p : Pattern) (guard : d0 p = 1) : d290 p ≤ (0 : Int) + d631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3387 (p : Pattern) (guard : d1134 p = 1) : d405 p ≤ (0 : Int) + d632 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d405, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d1134, d405, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d405, d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3386 p hg
    simpa only [d1134, d405, d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3388 (p : Pattern) (guard : d1134 p = 1) : d406 p ≤ (0 : Int) + d633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d406, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3361 p hg
    simpa only [d406, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d406, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3387 p hg
    simpa only [d406, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3389 (p : Pattern) (guard : d1134 p = 1) : d407 p ≤ (0 : Int) + d634 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d407, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d407, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d407, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d407, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3390 (p : Pattern) (guard : d1134 p = 1) : d408 p ≤ (0 : Int) + d635 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d408, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d408, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d408, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3389 p hg
    simpa only [d408, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3391 (p : Pattern) (guard : d0 p = 1) : d291 p ≤ (0 : Int) + d636 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3392 (p : Pattern) (guard : d1134 p = 1) : d409 p ≤ (0 : Int) + d637 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1134, d409, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d1134, d409, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d409, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d1134, d409, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3393 (p : Pattern) (guard : d1134 p = 1) : d410 p ≤ (0 : Int) + d638 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d410, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3369 p hg
    simpa only [d410, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d410, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d410, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3394 (p : Pattern) (guard : d1134 p = 1) : d411 p ≤ (0 : Int) + d639 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d411, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d411, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d411, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d411, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3395 (p : Pattern) (guard : d1134 p = 1) : d412 p ≤ (0 : Int) + d640 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d412, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d412, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d412, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d412, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3396 (p : Pattern) (guard : d1134 p = 1) : d413 p ≤ (0 : Int) + d641 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d413, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3390 p hg
    simpa only [d413, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d413, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d413, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3397 (p : Pattern) (guard : d1134 p = 1) : d414 p ≤ (0 : Int) + d642 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d414, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d414, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d414, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d414, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3398 (p : Pattern) (guard : d1134 p = 1) : d415 p ≤ (0 : Int) + d643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d415, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d415, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d415, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3387 p hg
    simpa only [d415, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3399 (p : Pattern) (guard : d1134 p = 1) : d416 p ≤ (0 : Int) + d644 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d416, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3398 p hg
    simpa only [d416, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d416, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3388 p hg
    simpa only [d416, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3400 (p : Pattern) (guard : d1134 p = 1) : d417 p ≤ (0 : Int) + d645 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d417, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d417, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d417, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d417, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3401 (p : Pattern) (guard : d1134 p = 1) : d418 p ≤ (0 : Int) + d646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d418, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d418, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d418, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d418, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3402 (p : Pattern) (guard : d1134 p = 1) : d419 p ≤ (0 : Int) + d647 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d419, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3401 p hg
    simpa only [d419, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d419, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d419, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3403 (p : Pattern) (guard : d1134 p = 1) : d420 p ≤ (0 : Int) + d648 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d420, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d420, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d420, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d420, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3404 (p : Pattern) (guard : d1134 p = 1) : d421 p ≤ (0 : Int) + d649 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d421, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3400 p hg
    simpa only [d421, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d421, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3403 p hg
    simpa only [d421, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3405 (p : Pattern) (guard : d1134 p = 1) : d422 p ≤ (0 : Int) + d650 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d422, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d422, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d422, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d422, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3406 (p : Pattern) (guard : d1134 p = 1) : d423 p ≤ (0 : Int) + d651 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d423, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d423, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d423, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d423, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3407 (p : Pattern) (guard : d1134 p = 1) : d424 p ≤ (0 : Int) + d652 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d424, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3389 p hg
    simpa only [d424, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d424, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d424, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3408 (p : Pattern) (guard : d1134 p = 1) : d425 p ≤ (0 : Int) + d653 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d425, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d425, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d425, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3366 p hg
    simpa only [d425, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3409 (p : Pattern) (guard : d1134 p = 1) : d426 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d426, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3407 p hg
    simpa only [d426, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d426, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3408 p hg
    simpa only [d426, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3410 (p : Pattern) (guard : d1134 p = 1) : d427 p ≤ (0 : Int) + d655 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d427, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3409 p hg
    simpa only [d427, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d427, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d427, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3411 (p : Pattern) (guard : d1134 p = 1) : d428 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d428, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d428, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d428, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3383 p hg
    simpa only [d428, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3412 (p : Pattern) (guard : d1134 p = 1) : d429 p ≤ (0 : Int) + d657 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d429, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d429, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d429, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d429, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3413 (p : Pattern) (guard : d1134 p = 1) : d430 p ≤ (0 : Int) + d658 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d430, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3385 p hg
    simpa only [d430, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1134 p = 1 := by simpa only [d430, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3412 p hg
    simpa only [d430, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3414 (p : Pattern) (guard : d769 p = 1) : d195 p ≤ (0 : Int) + d195 p := by
  omega
theorem compare3415 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare3416 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3415 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1350 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3417 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d179 p := by
  omega
theorem compare3418 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3417 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1359 p hg
    simpa only [d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3419 (p : Pattern) (guard : d770 p = 1) : d180 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3416 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3418 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3420 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare3421 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1362 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3422 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d181 p := by
  omega
theorem compare3423 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3424 (p : Pattern) (guard : d770 p = 1) : d182 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3421 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3423 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3425 (p : Pattern) (guard : d770 p = 1) : d183 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3419 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3426 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare3427 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3426 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1353 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3428 (p : Pattern) (guard : d770 p = 1) : d184 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3429 (p : Pattern) (guard : d770 p = 1) : d185 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3425 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3428 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3430 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d186 p := by
  omega
theorem compare3431 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3430 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1375 p hg
    simpa only [d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3432 (p : Pattern) (guard : d770 p = 1) : d187 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3431 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3433 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d188 p := by
  omega
theorem compare3434 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3433 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1380 p hg
    simpa only [d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3435 (p : Pattern) (guard : d770 p = 1) : d189 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3434 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3436 (p : Pattern) (guard : d770 p = 1) : d190 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3432 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3435 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3437 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d191 p := by
  omega
theorem compare3438 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3437 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1384 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3439 (p : Pattern) (guard : d770 p = 1) : d192 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3440 (p : Pattern) (guard : d770 p = 1) : d193 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3439 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3427 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3441 (p : Pattern) (guard : d770 p = 1) : d194 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3442 (p : Pattern) (guard : d770 p = 1) : d195 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3429 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3441 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3443 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3444 (p : Pattern) (guard : d742 p = 1) : d179 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3443 p hg
    simpa only [d742, d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3445 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3446 (p : Pattern) (guard : d742 p = 1) : d237 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3445 p hg
    simpa only [d742, d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3447 (p : Pattern) (guard : d742 p = 1) : d238 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3444 p hg
    simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3446 p hg
    simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3448 (p : Pattern) (guard : d742 p = 1) : d239 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3447 p hg
    simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3449 (p : Pattern) (guard : d742 p = 1) : d243 p ≤ (0 : Int) + d315 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d243, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3448 p hg
    simpa only [d243, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d243, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1578 p hg
    simpa only [d243, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3450 (p : Pattern) (guard : d742 p = 1) : d245 p ≤ (0 : Int) + d316 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d245, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3449 p hg
    simpa only [d245, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d245, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1580 p hg
    simpa only [d245, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3451 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3452 (p : Pattern) (guard : d742 p = 1) : d186 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d186, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d186, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d186, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3451 p hg
    simpa only [d742, d186, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3453 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3454 (p : Pattern) (guard : d742 p = 1) : d246 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d246, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d246, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d246, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3453 p hg
    simpa only [d742, d246, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3455 (p : Pattern) (guard : d742 p = 1) : d247 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d247, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3452 p hg
    simpa only [d247, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d247, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3454 p hg
    simpa only [d247, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3456 (p : Pattern) (guard : d742 p = 1) : d248 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d248, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d248, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d248, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d248, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3457 (p : Pattern) (guard : d742 p = 1) : d252 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d252, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3456 p hg
    simpa only [d252, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d252, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d252, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3458 (p : Pattern) (guard : d742 p = 1) : d257 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d257, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3457 p hg
    simpa only [d257, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d257, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1590 p hg
    simpa only [d257, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3459 (p : Pattern) (guard : d742 p = 1) : d258 p ≤ (0 : Int) + d319 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d258, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3450 p hg
    simpa only [d258, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d258, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3458 p hg
    simpa only [d258, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3460 (p : Pattern) (guard : d741 p = 1) : d64 p ≤ (0 : Int) + d64 p := by
  omega
theorem compare3461 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3462 (p : Pattern) (guard : d741 p = 1) : d179 p ≤ (0 : Int) + d122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3461 p hg
    simpa only [d741, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d741, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3463 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3464 (p : Pattern) (guard : d741 p = 1) : d237 p ≤ (0 : Int) + d129 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3463 p hg
    simpa only [d741, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d741, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3465 (p : Pattern) (guard : d741 p = 1) : d238 p ≤ (0 : Int) + d775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3462 p hg
    simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3464 p hg
    simpa only [d238, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3466 (p : Pattern) (guard : d741 p = 1) : d239 p ≤ (0 : Int) + d776 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3460 p hg
    simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3465 p hg
    simpa only [d239, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3467 (p : Pattern) (guard : d741 p = 1) : d68 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d741, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d741, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3468 (p : Pattern) (guard : d741 p = 1) : d69 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d741, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d741, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3469 (p : Pattern) (guard : d741 p = 1) : d70 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3467 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3468 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3470 (p : Pattern) (guard : d741 p = 1) : d181 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3443 p hg
    simpa only [d741, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d741, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3471 (p : Pattern) (guard : d741 p = 1) : d240 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3445 p hg
    simpa only [d741, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d741, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3472 (p : Pattern) (guard : d741 p = 1) : d241 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3470 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3471 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3473 (p : Pattern) (guard : d741 p = 1) : d242 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3469 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3472 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3474 (p : Pattern) (guard : d741 p = 1) : d243 p ≤ (0 : Int) + d778 p := by
  cases selected : p 133 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3466 p hg
    simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3473 p hg
    simpa only [d243, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3475 (p : Pattern) (guard : d0 p = 1) : d244 p ≤ (0 : Int) + d778 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3476 (p : Pattern) (guard : d774 p = 1) : d245 p ≤ (0 : Int) + d778 p := by
  cases selected : p 132 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d774, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3474 p hg
    simpa only [d774, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3475 p hg
    simpa only [d774, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3477 (p : Pattern) (guard : d741 p = 1) : d186 p ≤ (0 : Int) + d153 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d741, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d741, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3478 (p : Pattern) (guard : d741 p = 1) : d246 p ≤ (0 : Int) + d155 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d741, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d741, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3479 (p : Pattern) (guard : d741 p = 1) : d247 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3477 p hg
    simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3478 p hg
    simpa only [d247, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3480 (p : Pattern) (guard : d741 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare3481 (p : Pattern) (guard : d741 p = 1) : d248 p ≤ (0 : Int) + d784 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3479 p hg
    simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3480 p hg
    simpa only [d248, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3482 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3483 (p : Pattern) (guard : d741 p = 1) : d188 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3482 p hg
    simpa only [d741, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d741, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3484 (p : Pattern) (guard : d0 p = 1) : d147 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3485 (p : Pattern) (guard : d741 p = 1) : d249 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d741, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3484 p hg
    simpa only [d741, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d741, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d741, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3486 (p : Pattern) (guard : d741 p = 1) : d250 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3483 p hg
    simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3485 p hg
    simpa only [d250, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3487 (p : Pattern) (guard : d741 p = 1) : d251 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3486 p hg
    simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3480 p hg
    simpa only [d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3488 (p : Pattern) (guard : d741 p = 1) : d252 p ≤ (0 : Int) + d785 p := by
  cases selected : p 133 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3481 p hg
    simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d741 p = 1 := by simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3487 p hg
    simpa only [d252, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3489 (p : Pattern) (guard : d0 p = 1) : d256 p ≤ (0 : Int) + d785 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3490 (p : Pattern) (guard : d774 p = 1) : d257 p ≤ (0 : Int) + d785 p := by
  cases selected : p 132 with
  | false =>
    have hg : d741 p = 1 := by simpa only [d774, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3488 p hg
    simpa only [d774, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3489 p hg
    simpa only [d774, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3491 (p : Pattern) (guard : d774 p = 1) : d258 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 108 with
  | false =>
    have hg : d774 p = 1 := by simpa only [d258, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3476 p hg
    simpa only [d258, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d258, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3490 p hg
    simpa only [d258, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3492 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3493 (p : Pattern) (guard : d829 p = 1) : d57 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3494 (p : Pattern) (guard : d829 p = 1) : d61 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3495 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3492 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3494 p hg
    simpa only [d62, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3496 (p : Pattern) (guard : d829 p = 1) : d63 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3495 p hg
    simpa only [d63, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3497 (p : Pattern) (guard : d829 p = 1) : d64 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d64, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3498 (p : Pattern) (guard : d829 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare3499 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban12CostPartition
