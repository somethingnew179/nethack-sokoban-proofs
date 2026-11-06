/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons209
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29400 (p : Pattern) (guard : d5850 p = 1) : d3686 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3686, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d3686, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3686, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d3686, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29401 (p : Pattern) (guard : d5850 p = 1) : d3687 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3687, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29399 p hg
    simpa only [d3687, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3687, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29400 p hg
    simpa only [d3687, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29402 (p : Pattern) (guard : d5850 p = 1) : d3688 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3688, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29383 p hg
    simpa only [d3688, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3688, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3688, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29403 (p : Pattern) (guard : d5850 p = 1) : d3689 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3689, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29402 p hg
    simpa only [d3689, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3689, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3689, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29404 (p : Pattern) (guard : d5850 p = 1) : d3690 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3690, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29401 p hg
    simpa only [d3690, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3690, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29403 p hg
    simpa only [d3690, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29405 (p : Pattern) (guard : d5850 p = 1) : d3691 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3691, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29394 p hg
    simpa only [d3691, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3691, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3691, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29406 (p : Pattern) (guard : d5850 p = 1) : d3692 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3692, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29405 p hg
    simpa only [d3692, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3692, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3692, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29407 (p : Pattern) (guard : d5850 p = 1) : d3693 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3693, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29406 p hg
    simpa only [d3693, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3693, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3693, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29408 (p : Pattern) (guard : d5850 p = 1) : d3694 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3694, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29404 p hg
    simpa only [d3694, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3694, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29407 p hg
    simpa only [d3694, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29409 (p : Pattern) (guard : d5850 p = 1) : d3695 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3695, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29398 p hg
    simpa only [d3695, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3695, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29408 p hg
    simpa only [d3695, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29410 (p : Pattern) (guard : d5850 p = 1) : d3696 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3696, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29368 p hg
    simpa only [d3696, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3696, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3696, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29411 (p : Pattern) (guard : d5850 p = 1) : d3697 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3697, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29387 p hg
    simpa only [d3697, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3697, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29352 p hg
    simpa only [d3697, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29412 (p : Pattern) (guard : d5850 p = 1) : d3698 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3698, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29411 p hg
    simpa only [d3698, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3698, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3698, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29413 (p : Pattern) (guard : d5850 p = 1) : d3699 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3699, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29353 p hg
    simpa only [d3699, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3699, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3699, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29414 (p : Pattern) (guard : d5850 p = 1) : d3700 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3700, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29412 p hg
    simpa only [d3700, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3700, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29413 p hg
    simpa only [d3700, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29415 (p : Pattern) (guard : d5850 p = 1) : d3701 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3701, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29413 p hg
    simpa only [d3701, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3701, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3701, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29416 (p : Pattern) (guard : d5850 p = 1) : d3702 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3702, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29414 p hg
    simpa only [d3702, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3702, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29415 p hg
    simpa only [d3702, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29417 (p : Pattern) (guard : d5850 p = 1) : d3703 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3703, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29415 p hg
    simpa only [d3703, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3703, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3703, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29418 (p : Pattern) (guard : d5850 p = 1) : d3704 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3704, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29416 p hg
    simpa only [d3704, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3704, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29417 p hg
    simpa only [d3704, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29419 (p : Pattern) (guard : d5850 p = 1) : d3705 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3705, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3705, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3705, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29418 p hg
    simpa only [d3705, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29420 (p : Pattern) (guard : d5850 p = 1) : d3706 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3706, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29410 p hg
    simpa only [d3706, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3706, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29419 p hg
    simpa only [d3706, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29421 (p : Pattern) (guard : d5850 p = 1) : d3553 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29422 (p : Pattern) (guard : d5850 p = 1) : d3707 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3707, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29421 p hg
    simpa only [d3707, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3707, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d3707, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29423 (p : Pattern) (guard : d5850 p = 1) : d3708 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3708, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29422 p hg
    simpa only [d3708, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3708, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29269 p hg
    simpa only [d3708, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29424 (p : Pattern) (guard : d5850 p = 1) : d3709 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3709, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29423 p hg
    simpa only [d3709, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3709, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d3709, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29425 (p : Pattern) (guard : d5850 p = 1) : d3710 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3710, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d3710, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3710, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29337 p hg
    simpa only [d3710, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29426 (p : Pattern) (guard : d5850 p = 1) : d3711 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3711, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29425 p hg
    simpa only [d3711, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3711, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29339 p hg
    simpa only [d3711, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29427 (p : Pattern) (guard : d5850 p = 1) : d3712 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3712, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29426 p hg
    simpa only [d3712, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3712, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29354 p hg
    simpa only [d3712, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29428 (p : Pattern) (guard : d5850 p = 1) : d3713 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3713, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29427 p hg
    simpa only [d3713, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3713, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29366 p hg
    simpa only [d3713, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29429 (p : Pattern) (guard : d5850 p = 1) : d3714 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3714, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29424 p hg
    simpa only [d3714, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3714, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29428 p hg
    simpa only [d3714, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29430 (p : Pattern) (guard : d5850 p = 1) : d3715 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3715, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29429 p hg
    simpa only [d3715, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3715, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3715, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29431 (p : Pattern) (guard : d5850 p = 1) : d3716 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3716, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3716, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3716, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3716, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29432 (p : Pattern) (guard : d5850 p = 1) : d3717 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3717, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29430 p hg
    simpa only [d3717, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3717, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29431 p hg
    simpa only [d3717, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29433 (p : Pattern) (guard : d5850 p = 1) : d3718 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3718, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29420 p hg
    simpa only [d3718, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3718, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29432 p hg
    simpa only [d3718, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29434 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29435 (p : Pattern) (guard : d5843 p = 1) : d2051 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29434 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29436 (p : Pattern) (guard : d5843 p = 1) : d3719 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3719, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29435 p hg
    simpa only [d3719, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3719, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d3719, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29437 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29438 (p : Pattern) (guard : d5850 p = 1) : d3720 p ≤ (0 : Int) + d2653 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3720, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29436 p hg
    simpa only [d5850, d3720, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3720, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29437 p hg
    simpa only [d5850, d3720, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29439 (p : Pattern) (guard : d5850 p = 1) : d3721 p ≤ (0 : Int) + d2654 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3721, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29438 p hg
    simpa only [d3721, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3721, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3721, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29440 (p : Pattern) (guard : d5850 p = 1) : d3722 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3722, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29439 p hg
    simpa only [d3722, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3722, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3722, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29441 (p : Pattern) (guard : d5850 p = 1) : d3723 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3723, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29440 p hg
    simpa only [d3723, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3723, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d3723, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29442 (p : Pattern) (guard : d5850 p = 1) : d3724 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3724, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29441 p hg
    simpa only [d3724, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3724, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d3724, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29443 (p : Pattern) (guard : d5850 p = 1) : d3725 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3725, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29442 p hg
    simpa only [d3725, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3725, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d3725, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29444 (p : Pattern) (guard : d5850 p = 1) : d3726 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3726, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29443 p hg
    simpa only [d3726, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3726, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29269 p hg
    simpa only [d3726, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29445 (p : Pattern) (guard : d5850 p = 1) : d3727 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3727, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29444 p hg
    simpa only [d3727, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3727, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d3727, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29446 (p : Pattern) (guard : d5850 p = 1) : d3710 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3710, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d3710, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3710, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29337 p hg
    simpa only [d3710, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29447 (p : Pattern) (guard : d5850 p = 1) : d3711 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3711, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29446 p hg
    simpa only [d3711, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3711, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29339 p hg
    simpa only [d3711, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29448 (p : Pattern) (guard : d5850 p = 1) : d3712 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3712, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29447 p hg
    simpa only [d3712, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3712, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29354 p hg
    simpa only [d3712, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29449 (p : Pattern) (guard : d5850 p = 1) : d3713 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3713, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29448 p hg
    simpa only [d3713, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3713, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29366 p hg
    simpa only [d3713, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29450 (p : Pattern) (guard : d5850 p = 1) : d3728 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3728, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29445 p hg
    simpa only [d3728, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3728, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29449 p hg
    simpa only [d3728, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29451 (p : Pattern) (guard : d5850 p = 1) : d3729 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3729, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29450 p hg
    simpa only [d3729, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3729, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3729, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29452 (p : Pattern) (guard : d5850 p = 1) : d3730 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3730, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29451 p hg
    simpa only [d3730, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3730, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29419 p hg
    simpa only [d3730, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29453 (p : Pattern) (guard : d5850 p = 1) : d3707 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3707, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d3707, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3707, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d3707, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29454 (p : Pattern) (guard : d5850 p = 1) : d3708 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3708, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29453 p hg
    simpa only [d3708, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3708, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29269 p hg
    simpa only [d3708, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29455 (p : Pattern) (guard : d5850 p = 1) : d3709 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3709, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29454 p hg
    simpa only [d3709, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3709, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29314 p hg
    simpa only [d3709, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29456 (p : Pattern) (guard : d5850 p = 1) : d3714 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3714, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29455 p hg
    simpa only [d3714, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3714, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29428 p hg
    simpa only [d3714, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29457 (p : Pattern) (guard : d5850 p = 1) : d3715 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3715, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29456 p hg
    simpa only [d3715, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3715, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29409 p hg
    simpa only [d3715, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29458 (p : Pattern) (guard : d5850 p = 1) : d3717 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3717, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29457 p hg
    simpa only [d3717, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3717, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29431 p hg
    simpa only [d3717, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29459 (p : Pattern) (guard : d5850 p = 1) : d3731 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3731, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29452 p hg
    simpa only [d3731, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3731, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29458 p hg
    simpa only [d3731, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29460 (p : Pattern) (guard : d5850 p = 1) : d3732 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3732, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29433 p hg
    simpa only [d3732, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3732, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29459 p hg
    simpa only [d3732, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29461 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29462 (p : Pattern) (guard : d5843 p = 1) : d428 p ≤ (0 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29461 p hg
    simpa only [d5843, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29463 (p : Pattern) (guard : d5843 p = 1) : d3733 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3733, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29462 p hg
    simpa only [d3733, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3733, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20132 p hg
    simpa only [d3733, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29464 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29465 (p : Pattern) (guard : d5850 p = 1) : d3734 p ≤ (0 : Int) + d2676 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3734, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29463 p hg
    simpa only [d5850, d3734, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3734, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29464 p hg
    simpa only [d5850, d3734, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29466 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20132 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29467 (p : Pattern) (guard : d5850 p = 1) : d102 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5850, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29468 (p : Pattern) (guard : d5850 p = 1) : d3735 p ≤ (0 : Int) + d2678 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3735, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29465 p hg
    simpa only [d3735, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3735, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d3735, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29469 (p : Pattern) (guard : d0 p = 1) : d3736 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29470 (p : Pattern) (guard : d5850 p = 1) : d3737 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3737, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5850, d3737, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3737, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5850, d3737, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29471 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d1939 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26436 p hg
    simpa only [d5843, d102, d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29472 (p : Pattern) (guard : d5843 p = 1) : d3736 p ≤ (0 : Int) + d1940 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3736, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29471 p hg
    simpa only [d3736, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3736, d1940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d3736, d1940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29473 (p : Pattern) (guard : d5850 p = 1) : d3736 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5850, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29474 (p : Pattern) (guard : d5850 p = 1) : d3738 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3738, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29470 p hg
    simpa only [d3738, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3738, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29473 p hg
    simpa only [d3738, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29475 (p : Pattern) (guard : d5850 p = 1) : d3739 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3739, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29468 p hg
    simpa only [d3739, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3739, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d3739, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29476 (p : Pattern) (guard : d0 p = 1) : d3740 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29477 (p : Pattern) (guard : d5850 p = 1) : d3741 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3741, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5850, d3741, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3741, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5850, d3741, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29478 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d1872 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d5843, d102, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26447 p hg
    simpa only [d5843, d102, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29479 (p : Pattern) (guard : d5843 p = 1) : d3740 p ≤ (0 : Int) + d1873 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3740, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29478 p hg
    simpa only [d3740, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3740, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20198 p hg
    simpa only [d3740, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29480 (p : Pattern) (guard : d5850 p = 1) : d3740 p ≤ (0 : Int) + d2682 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29479 p hg
    simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5850, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29481 (p : Pattern) (guard : d5850 p = 1) : d3742 p ≤ (0 : Int) + d2683 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3742, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29477 p hg
    simpa only [d3742, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3742, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29480 p hg
    simpa only [d3742, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29482 (p : Pattern) (guard : d5850 p = 1) : d3743 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3743, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29481 p hg
    simpa only [d3743, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3743, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3743, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29483 (p : Pattern) (guard : d5850 p = 1) : d3744 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3744, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29475 p hg
    simpa only [d3744, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3744, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29482 p hg
    simpa only [d3744, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29484 (p : Pattern) (guard : d5850 p = 1) : d3745 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3745, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d3745, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3745, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29474 p hg
    simpa only [d3745, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29485 (p : Pattern) (guard : d5850 p = 1) : d3746 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3746, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29484 p hg
    simpa only [d3746, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3746, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29482 p hg
    simpa only [d3746, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29486 (p : Pattern) (guard : d5850 p = 1) : d3747 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3747, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29483 p hg
    simpa only [d3747, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3747, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29485 p hg
    simpa only [d3747, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29487 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20166 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29488 (p : Pattern) (guard : d5850 p = 1) : d106 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5850, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29489 (p : Pattern) (guard : d0 p = 1) : d3748 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29490 (p : Pattern) (guard : d5850 p = 1) : d3749 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3749, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5850, d3749, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3749, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d5850, d3749, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29491 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d1963 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d106, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d5843, d106, d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29492 (p : Pattern) (guard : d5843 p = 1) : d3748 p ≤ (0 : Int) + d1964 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3748, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29491 p hg
    simpa only [d3748, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3748, d1964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d3748, d1964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29493 (p : Pattern) (guard : d5850 p = 1) : d3748 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d5850, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29494 (p : Pattern) (guard : d5850 p = 1) : d3750 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3750, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29490 p hg
    simpa only [d3750, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3750, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29493 p hg
    simpa only [d3750, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29495 (p : Pattern) (guard : d5850 p = 1) : d3751 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3751, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29488 p hg
    simpa only [d3751, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3751, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29494 p hg
    simpa only [d3751, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29496 (p : Pattern) (guard : d0 p = 1) : d3752 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29497 (p : Pattern) (guard : d5850 p = 1) : d3753 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3753, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5850, d3753, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3753, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d5850, d3753, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29498 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d1880 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d106, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d5843, d106, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29499 (p : Pattern) (guard : d5843 p = 1) : d3752 p ≤ (0 : Int) + d1881 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3752, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29498 p hg
    simpa only [d3752, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3752, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d3752, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29500 (p : Pattern) (guard : d5850 p = 1) : d3752 p ≤ (0 : Int) + d2693 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29499 p hg
    simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d5850, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29501 (p : Pattern) (guard : d5850 p = 1) : d3754 p ≤ (0 : Int) + d2694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3754, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29497 p hg
    simpa only [d3754, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3754, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29500 p hg
    simpa only [d3754, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29502 (p : Pattern) (guard : d5850 p = 1) : d3755 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3755, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29501 p hg
    simpa only [d3755, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3755, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3755, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29503 (p : Pattern) (guard : d5850 p = 1) : d3756 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3756, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29495 p hg
    simpa only [d3756, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3756, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29502 p hg
    simpa only [d3756, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29504 (p : Pattern) (guard : d5850 p = 1) : d3757 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3757, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29485 p hg
    simpa only [d3757, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3757, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29503 p hg
    simpa only [d3757, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29505 (p : Pattern) (guard : d5850 p = 1) : d3758 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3758, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29486 p hg
    simpa only [d3758, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3758, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29504 p hg
    simpa only [d3758, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29506 (p : Pattern) (guard : d5850 p = 1) : d3759 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3759, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29348 p hg
    simpa only [d3759, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3759, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3759, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29507 (p : Pattern) (guard : d5850 p = 1) : d3760 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3760, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29504 p hg
    simpa only [d3760, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3760, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29506 p hg
    simpa only [d3760, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29508 (p : Pattern) (guard : d5850 p = 1) : d3761 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3761, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29505 p hg
    simpa only [d3761, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3761, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29507 p hg
    simpa only [d3761, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29509 (p : Pattern) (guard : d0 p = 1) : d3762 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29510 (p : Pattern) (guard : d5850 p = 1) : d3763 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3763, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5850, d3763, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3763, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29509 p hg
    simpa only [d5850, d3763, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29511 (p : Pattern) (guard : d5850 p = 1) : d3764 p ≤ (0 : Int) + d2679 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3764, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29472 p hg
    simpa only [d5850, d3764, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3764, d2679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d5850, d3764, d2679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29512 (p : Pattern) (guard : d5850 p = 1) : d3765 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3765, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29510 p hg
    simpa only [d3765, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3765, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29511 p hg
    simpa only [d3765, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29513 (p : Pattern) (guard : d5850 p = 1) : d3766 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3766, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29467 p hg
    simpa only [d3766, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3766, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29512 p hg
    simpa only [d3766, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29514 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20198 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29515 (p : Pattern) (guard : d0 p = 1) : d3767 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29516 (p : Pattern) (guard : d5850 p = 1) : d3768 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3768, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29514 p hg
    simpa only [d5850, d3768, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3768, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29515 p hg
    simpa only [d5850, d3768, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29517 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (0 : Int) + d1894 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d115, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26453 p hg
    simpa only [d5843, d115, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29518 (p : Pattern) (guard : d5843 p = 1) : d3769 p ≤ (0 : Int) + d1895 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3769, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29517 p hg
    simpa only [d3769, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3769, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d3769, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29519 (p : Pattern) (guard : d5850 p = 1) : d3770 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3770, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29518 p hg
    simpa only [d5850, d3770, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3770, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17337 p hg
    simpa only [d5850, d3770, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29520 (p : Pattern) (guard : d5850 p = 1) : d3771 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3771, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29516 p hg
    simpa only [d3771, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3771, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29519 p hg
    simpa only [d3771, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29521 (p : Pattern) (guard : d5850 p = 1) : d3772 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3772, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29520 p hg
    simpa only [d3772, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3772, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3772, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29522 (p : Pattern) (guard : d5850 p = 1) : d3773 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3773, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d3773, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3773, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29521 p hg
    simpa only [d3773, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29523 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26454 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20209 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29524 (p : Pattern) (guard : d5850 p = 1) : d3774 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3774, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29523 p hg
    simpa only [d5850, d3774, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3774, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5850, d3774, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29525 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (0 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d119, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29526 (p : Pattern) (guard : d5843 p = 1) : d3775 p ≤ (0 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3775, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29525 p hg
    simpa only [d3775, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3775, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19939 p hg
    simpa only [d3775, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29527 (p : Pattern) (guard : d5850 p = 1) : d3776 p ≤ (0 : Int) + d2708 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3776, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29526 p hg
    simpa only [d5850, d3776, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3776, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5850, d3776, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29528 (p : Pattern) (guard : d5850 p = 1) : d3777 p ≤ (0 : Int) + d2709 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3777, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29524 p hg
    simpa only [d3777, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3777, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29527 p hg
    simpa only [d3777, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29529 (p : Pattern) (guard : d5850 p = 1) : d3778 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3778, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29528 p hg
    simpa only [d3778, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3778, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3778, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29530 (p : Pattern) (guard : d5850 p = 1) : d3779 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3779, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d3779, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3779, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29529 p hg
    simpa only [d3779, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29531 (p : Pattern) (guard : d5850 p = 1) : d3780 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3780, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29522 p hg
    simpa only [d3780, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3780, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29530 p hg
    simpa only [d3780, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29532 (p : Pattern) (guard : d5850 p = 1) : d3781 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3781, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29513 p hg
    simpa only [d3781, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3781, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3781, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29533 (p : Pattern) (guard : d0 p = 1) : d3782 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29534 (p : Pattern) (guard : d5850 p = 1) : d3783 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3783, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5850, d3783, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3783, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29533 p hg
    simpa only [d5850, d3783, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29535 (p : Pattern) (guard : d5850 p = 1) : d3784 p ≤ (0 : Int) + d2690 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3784, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29492 p hg
    simpa only [d5850, d3784, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3784, d2690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17409 p hg
    simpa only [d5850, d3784, d2690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29536 (p : Pattern) (guard : d5850 p = 1) : d3785 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3785, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29534 p hg
    simpa only [d3785, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3785, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29535 p hg
    simpa only [d3785, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29537 (p : Pattern) (guard : d5850 p = 1) : d3786 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3786, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29488 p hg
    simpa only [d3786, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3786, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29536 p hg
    simpa only [d3786, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29538 (p : Pattern) (guard : d5850 p = 1) : d3787 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3787, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29537 p hg
    simpa only [d3787, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3787, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3787, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29539 (p : Pattern) (guard : d5850 p = 1) : d3788 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3788, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29532 p hg
    simpa only [d3788, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3788, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29538 p hg
    simpa only [d3788, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
