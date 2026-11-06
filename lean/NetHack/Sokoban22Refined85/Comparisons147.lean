/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20580 (p : Pattern) (guard : d5850 p = 1) : d2544 p ≤ (0 : Int) + d3589 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2544, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2544, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2544, d3589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20579 p hg
    simpa only [d2544, d3589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20581 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d364 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20582 (p : Pattern) (guard : d5850 p = 1) : d2545 p ≤ (0 : Int) + d3590 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2545, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d5850, d2545, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2545, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20581 p hg
    simpa only [d5850, d2545, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20583 (p : Pattern) (guard : d5843 p = 1) : d1721 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1721, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d5843, d1721, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1721, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d1721, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20584 (p : Pattern) (guard : d5843 p = 1) : d1722 p ≤ (0 : Int) + d3591 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1722, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20583 p hg
    simpa only [d1722, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1722, d3591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d1722, d3591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20585 (p : Pattern) (guard : d5850 p = 1) : d2546 p ≤ (0 : Int) + d3592 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2546, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20584 p hg
    simpa only [d5850, d2546, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2546, d3592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20581 p hg
    simpa only [d5850, d2546, d3592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20586 (p : Pattern) (guard : d5850 p = 1) : d2547 p ≤ (0 : Int) + d3593 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2547, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20582 p hg
    simpa only [d2547, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2547, d3593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20585 p hg
    simpa only [d2547, d3593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20587 (p : Pattern) (guard : d5850 p = 1) : d2548 p ≤ (0 : Int) + d3594 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2548, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20586 p hg
    simpa only [d2548, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2548, d3594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2548, d3594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20588 (p : Pattern) (guard : d5850 p = 1) : d2549 p ≤ (0 : Int) + d3595 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2549, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2549, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2549, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20587 p hg
    simpa only [d2549, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20589 (p : Pattern) (guard : d5850 p = 1) : d2550 p ≤ (0 : Int) + d3596 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2550, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20580 p hg
    simpa only [d2550, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2550, d3596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20588 p hg
    simpa only [d2550, d3596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20590 (p : Pattern) (guard : d5850 p = 1) : d2551 p ≤ (0 : Int) + d3597 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2551, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d5850, d2551, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2551, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5850, d2551, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20591 (p : Pattern) (guard : d5843 p = 1) : d327 p ≤ (0 : Int) + d327 p := by
  omega
theorem compare20592 (p : Pattern) (guard : d5850 p = 1) : d332 p ≤ (0 : Int) + d327 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5850, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20593 (p : Pattern) (guard : d5850 p = 1) : d2552 p ≤ (0 : Int) + d3598 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2552, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20590 p hg
    simpa only [d2552, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2552, d3598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20592 p hg
    simpa only [d2552, d3598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20594 (p : Pattern) (guard : d5850 p = 1) : d2553 p ≤ (0 : Int) + d3599 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2553, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20593 p hg
    simpa only [d2553, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2553, d3599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2553, d3599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20595 (p : Pattern) (guard : d5850 p = 1) : d2554 p ≤ (0 : Int) + d3600 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2554, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2554, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2554, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20594 p hg
    simpa only [d2554, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20596 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3601 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20597 (p : Pattern) (guard : d5850 p = 1) : d2520 p ≤ (0 : Int) + d3602 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2520, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5850, d2520, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2520, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20596 p hg
    simpa only [d5850, d2520, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20598 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d339 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20599 (p : Pattern) (guard : d5850 p = 1) : d2521 p ≤ (0 : Int) + d3603 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2521, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d5850, d2521, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2521, d3603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20598 p hg
    simpa only [d5850, d2521, d3603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20600 (p : Pattern) (guard : d5850 p = 1) : d2522 p ≤ (0 : Int) + d3604 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20597 p hg
    simpa only [d2522, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20599 p hg
    simpa only [d2522, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20601 (p : Pattern) (guard : d5850 p = 1) : d2523 p ≤ (0 : Int) + d3605 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20534 p hg
    simpa only [d2523, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20600 p hg
    simpa only [d2523, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20602 (p : Pattern) (guard : d5850 p = 1) : d2555 p ≤ (0 : Int) + d3606 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2555, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20601 p hg
    simpa only [d2555, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2555, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2555, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20603 (p : Pattern) (guard : d5850 p = 1) : d2556 p ≤ (0 : Int) + d3607 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2556, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20595 p hg
    simpa only [d2556, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2556, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d2556, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20604 (p : Pattern) (guard : d5850 p = 1) : d2557 p ≤ (0 : Int) + d3608 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2557, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20589 p hg
    simpa only [d2557, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2557, d3608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20603 p hg
    simpa only [d2557, d3608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20605 (p : Pattern) (guard : d5850 p = 1) : d2558 p ≤ (0 : Int) + d3609 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2558, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2558, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2558, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2558, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20606 (p : Pattern) (guard : d5850 p = 1) : d2559 p ≤ (0 : Int) + d3610 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2559, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20605 p hg
    simpa only [d2559, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2559, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d2559, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20607 (p : Pattern) (guard : d5850 p = 1) : d2560 p ≤ (0 : Int) + d3611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2560, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20555 p hg
    simpa only [d2560, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2560, d3611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2560, d3611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20608 (p : Pattern) (guard : d5850 p = 1) : d2561 p ≤ (0 : Int) + d3612 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2561, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20607 p hg
    simpa only [d2561, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2561, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2561, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20609 (p : Pattern) (guard : d5850 p = 1) : d2562 p ≤ (0 : Int) + d3613 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2562, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20606 p hg
    simpa only [d2562, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2562, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20608 p hg
    simpa only [d2562, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20610 (p : Pattern) (guard : d5850 p = 1) : d2563 p ≤ (0 : Int) + d3614 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2563, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20604 p hg
    simpa only [d2563, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2563, d3614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20609 p hg
    simpa only [d2563, d3614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20611 (p : Pattern) (guard : d5850 p = 1) : d2564 p ≤ (0 : Int) + d3615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2564, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20565 p hg
    simpa only [d2564, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2564, d3615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20610 p hg
    simpa only [d2564, d3615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20612 (p : Pattern) (guard : d0 p = 1) : d329 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20613 (p : Pattern) (guard : d5850 p = 1) : d2565 p ≤ (0 : Int) + d3617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2565, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19964 p hg
    simpa only [d5850, d2565, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2565, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20612 p hg
    simpa only [d5850, d2565, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20614 (p : Pattern) (guard : d5850 p = 1) : d2566 p ≤ (0 : Int) + d3618 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2566, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20613 p hg
    simpa only [d2566, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2566, d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2566, d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20615 (p : Pattern) (guard : d5850 p = 1) : d2567 p ≤ (0 : Int) + d3619 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2567, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20614 p hg
    simpa only [d2567, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2567, d3619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2567, d3619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20616 (p : Pattern) (guard : d5850 p = 1) : d2568 p ≤ (0 : Int) + d3620 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2568, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20615 p hg
    simpa only [d2568, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2568, d3620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20524 p hg
    simpa only [d2568, d3620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20617 (p : Pattern) (guard : d5850 p = 1) : d2540 p ≤ (0 : Int) + d30 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19972 p hg
    simpa only [d5850, d2540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20618 (p : Pattern) (guard : d5850 p = 1) : d2540 p ≤ (0 : Int) + d3621 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2540, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5850, d2540, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2540, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19977 p hg
    simpa only [d5850, d2540, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20619 (p : Pattern) (guard : d5850 p = 1) : d2541 p ≤ (0 : Int) + d3585 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19977 p hg
    simpa only [d5850, d2541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20620 (p : Pattern) (guard : d5850 p = 1) : d2542 p ≤ (0 : Int) + d3622 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20618 p hg
    simpa only [d2542, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20619 p hg
    simpa only [d2542, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20621 (p : Pattern) (guard : d5850 p = 1) : d2569 p ≤ (0 : Int) + d3623 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20617 p hg
    simpa only [d2569, d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20620 p hg
    simpa only [d2569, d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20622 (p : Pattern) (guard : d5850 p = 1) : d2540 p ≤ (0 : Int) + d3625 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2540, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19918 p hg
    simpa only [d5850, d2540, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2540, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19983 p hg
    simpa only [d5850, d2540, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20623 (p : Pattern) (guard : d5843 p = 1) : d1742 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1742, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d1742, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1742, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d1742, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20624 (p : Pattern) (guard : d5843 p = 1) : d1743 p ≤ (0 : Int) + d3624 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1743, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20623 p hg
    simpa only [d1743, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1743, d3624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d1743, d3624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20625 (p : Pattern) (guard : d5850 p = 1) : d2570 p ≤ (0 : Int) + d3624 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20624 p hg
    simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19983 p hg
    simpa only [d5850, d2570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20626 (p : Pattern) (guard : d5850 p = 1) : d2571 p ≤ (0 : Int) + d3626 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2571, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20622 p hg
    simpa only [d2571, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2571, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20625 p hg
    simpa only [d2571, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20627 (p : Pattern) (guard : d5850 p = 1) : d2572 p ≤ (0 : Int) + d3627 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2572, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20626 p hg
    simpa only [d2572, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2572, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2572, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20628 (p : Pattern) (guard : d5850 p = 1) : d2573 p ≤ (0 : Int) + d3628 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2573, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20621 p hg
    simpa only [d2573, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2573, d3628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20627 p hg
    simpa only [d2573, d3628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20629 (p : Pattern) (guard : d5850 p = 1) : d2574 p ≤ (0 : Int) + d3629 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2574, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20616 p hg
    simpa only [d2574, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2574, d3629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20628 p hg
    simpa only [d2574, d3629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20630 (p : Pattern) (guard : d5850 p = 1) : d2575 p ≤ (0 : Int) + d3630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2575, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20547 p hg
    simpa only [d2575, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2575, d3630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20562 p hg
    simpa only [d2575, d3630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20631 (p : Pattern) (guard : d5850 p = 1) : d2576 p ≤ (0 : Int) + d3631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2576, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20629 p hg
    simpa only [d2576, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2576, d3631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20630 p hg
    simpa only [d2576, d3631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20632 (p : Pattern) (guard : d5850 p = 1) : d2577 p ≤ (0 : Int) + d57 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5850, d2577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20633 (p : Pattern) (guard : d5850 p = 1) : d2577 p ≤ (0 : Int) + d3632 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2577, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19993 p hg
    simpa only [d5850, d2577, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2577, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5850, d2577, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20634 (p : Pattern) (guard : d5843 p = 1) : d329 p ≤ (0 : Int) + d329 p := by
  omega
theorem compare20635 (p : Pattern) (guard : d5850 p = 1) : d330 p ≤ (0 : Int) + d329 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d5850, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20636 (p : Pattern) (guard : d5850 p = 1) : d2578 p ≤ (0 : Int) + d3633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2578, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20633 p hg
    simpa only [d2578, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2578, d3633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20635 p hg
    simpa only [d2578, d3633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20637 (p : Pattern) (guard : d5850 p = 1) : d2579 p ≤ (0 : Int) + d3634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2579, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20632 p hg
    simpa only [d2579, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2579, d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20636 p hg
    simpa only [d2579, d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20638 (p : Pattern) (guard : d5850 p = 1) : d2580 p ≤ (0 : Int) + d3635 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2580, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20636 p hg
    simpa only [d2580, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2580, d3635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2580, d3635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20639 (p : Pattern) (guard : d5850 p = 1) : d2581 p ≤ (0 : Int) + d3636 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2581, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20637 p hg
    simpa only [d2581, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2581, d3636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20638 p hg
    simpa only [d2581, d3636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20640 (p : Pattern) (guard : d5850 p = 1) : d2582 p ≤ (0 : Int) + d3637 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2582, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20547 p hg
    simpa only [d2582, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2582, d3637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2582, d3637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20641 (p : Pattern) (guard : d5850 p = 1) : d2551 p ≤ (0 : Int) + d39 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19940 p hg
    simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5850, d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20642 (p : Pattern) (guard : d5850 p = 1) : d2583 p ≤ (0 : Int) + d3638 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2583, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20641 p hg
    simpa only [d2583, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2583, d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20593 p hg
    simpa only [d2583, d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20643 (p : Pattern) (guard : d5850 p = 1) : d2584 p ≤ (0 : Int) + d3639 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2584, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20642 p hg
    simpa only [d2584, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2584, d3639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20594 p hg
    simpa only [d2584, d3639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20644 (p : Pattern) (guard : d5850 p = 1) : d2585 p ≤ (0 : Int) + d3640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2585, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2585, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2585, d3640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2585, d3640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20645 (p : Pattern) (guard : d5850 p = 1) : d2586 p ≤ (0 : Int) + d3641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2586, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20640 p hg
    simpa only [d2586, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2586, d3641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2586, d3641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20646 (p : Pattern) (guard : d5850 p = 1) : d2587 p ≤ (0 : Int) + d3642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2587, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20631 p hg
    simpa only [d2587, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2587, d3642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20645 p hg
    simpa only [d2587, d3642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20647 (p : Pattern) (guard : d5850 p = 1) : d2569 p ≤ (0 : Int) + d3643 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20617 p hg
    simpa only [d2569, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20578 p hg
    simpa only [d2569, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20648 (p : Pattern) (guard : d5850 p = 1) : d2588 p ≤ (0 : Int) + d3644 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2588, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d2588, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2588, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2588, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20649 (p : Pattern) (guard : d5850 p = 1) : d2589 p ≤ (0 : Int) + d3645 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2589, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20588 p hg
    simpa only [d2589, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2589, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20648 p hg
    simpa only [d2589, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20650 (p : Pattern) (guard : d5850 p = 1) : d2590 p ≤ (0 : Int) + d3646 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2590, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d2590, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2590, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20607 p hg
    simpa only [d2590, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20651 (p : Pattern) (guard : d5850 p = 1) : d2591 p ≤ (0 : Int) + d3647 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2591, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20649 p hg
    simpa only [d2591, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2591, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20650 p hg
    simpa only [d2591, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20652 (p : Pattern) (guard : d5850 p = 1) : d2592 p ≤ (0 : Int) + d3648 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2592, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20637 p hg
    simpa only [d2592, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2592, d3648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2592, d3648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20653 (p : Pattern) (guard : d5850 p = 1) : d2593 p ≤ (0 : Int) + d3649 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2593, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d2593, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2593, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20652 p hg
    simpa only [d2593, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20654 (p : Pattern) (guard : d5850 p = 1) : d2594 p ≤ (0 : Int) + d3650 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2594, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20642 p hg
    simpa only [d2594, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2594, d3650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2594, d3650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20655 (p : Pattern) (guard : d5850 p = 1) : d2595 p ≤ (0 : Int) + d3651 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2595, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20654 p hg
    simpa only [d2595, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2595, d3651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2595, d3651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20656 (p : Pattern) (guard : d5850 p = 1) : d2596 p ≤ (0 : Int) + d3652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2596, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20653 p hg
    simpa only [d2596, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2596, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20655 p hg
    simpa only [d2596, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20657 (p : Pattern) (guard : d5850 p = 1) : d2597 p ≤ (0 : Int) + d3653 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2597, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20651 p hg
    simpa only [d2597, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2597, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20656 p hg
    simpa only [d2597, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20658 (p : Pattern) (guard : d5850 p = 1) : d2598 p ≤ (0 : Int) + d3654 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2598, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20646 p hg
    simpa only [d2598, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2598, d3654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20657 p hg
    simpa only [d2598, d3654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20659 (p : Pattern) (guard : d5850 p = 1) : d2599 p ≤ (0 : Int) + d3655 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2599, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20611 p hg
    simpa only [d2599, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2599, d3655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20658 p hg
    simpa only [d2599, d3655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20660 (p : Pattern) (guard : d5850 p = 1) : d2506 p ≤ (0 : Int) + d3656 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2506, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d5850, d2506, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2506, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20566 p hg
    simpa only [d5850, d2506, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20661 (p : Pattern) (guard : d5850 p = 1) : d2507 p ≤ (0 : Int) + d3657 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20567 p hg
    simpa only [d2507, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20660 p hg
    simpa only [d2507, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20662 (p : Pattern) (guard : d5850 p = 1) : d2518 p ≤ (0 : Int) + d3658 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2518, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20661 p hg
    simpa only [d2518, d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20663 (p : Pattern) (guard : d5850 p = 1) : d2600 p ≤ (0 : Int) + d3659 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20516 p hg
    simpa only [d2600, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2600, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20664 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3660 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20662 p hg
    simpa only [d2601, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20663 p hg
    simpa only [d2601, d3660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20665 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20666 (p : Pattern) (guard : d5850 p = 1) : d2506 p ≤ (0 : Int) + d3662 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2506, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20514 p hg
    simpa only [d5850, d2506, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2506, d3662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20665 p hg
    simpa only [d5850, d2506, d3662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20667 (p : Pattern) (guard : d5850 p = 1) : d2507 p ≤ (0 : Int) + d3663 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20567 p hg
    simpa only [d2507, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2507, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20666 p hg
    simpa only [d2507, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20668 (p : Pattern) (guard : d5850 p = 1) : d2600 p ≤ (0 : Int) + d3664 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20667 p hg
    simpa only [d2600, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2600, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20669 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3665 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2601, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20668 p hg
    simpa only [d2601, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20670 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20664 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20669 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20671 (p : Pattern) (guard : d5850 p = 1) : d2600 p ≤ (0 : Int) + d3667 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20570 p hg
    simpa only [d2600, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2600, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20672 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3668 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20571 p hg
    simpa only [d2601, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20671 p hg
    simpa only [d2601, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20673 (p : Pattern) (guard : d5850 p = 1) : d2602 p ≤ (0 : Int) + d3669 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2602, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20600 p hg
    simpa only [d2602, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2602, d3669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2602, d3669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20674 (p : Pattern) (guard : d5850 p = 1) : d2603 p ≤ (0 : Int) + d3670 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2603, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20601 p hg
    simpa only [d2603, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2603, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20673 p hg
    simpa only [d2603, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20675 (p : Pattern) (guard : d5850 p = 1) : d2604 p ≤ (0 : Int) + d3671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2604, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20672 p hg
    simpa only [d2604, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2604, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d2604, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20676 (p : Pattern) (guard : d5850 p = 1) : d2605 p ≤ (0 : Int) + d3672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2605, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20670 p hg
    simpa only [d2605, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2605, d3672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20675 p hg
    simpa only [d2605, d3672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20677 (p : Pattern) (guard : d5850 p = 1) : d2606 p ≤ (0 : Int) + d3673 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2606, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20554 p hg
    simpa only [d2606, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2606, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2606, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20678 (p : Pattern) (guard : d5850 p = 1) : d2607 p ≤ (0 : Int) + d3674 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2607, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20555 p hg
    simpa only [d2607, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2607, d3674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20677 p hg
    simpa only [d2607, d3674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20679 (p : Pattern) (guard : d5850 p = 1) : d2608 p ≤ (0 : Int) + d3675 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2608, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2608, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2608, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2608, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20680 (p : Pattern) (guard : d5850 p = 1) : d2609 p ≤ (0 : Int) + d3676 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2609, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20675 p hg
    simpa only [d2609, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2609, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20679 p hg
    simpa only [d2609, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20681 (p : Pattern) (guard : d5850 p = 1) : d2610 p ≤ (0 : Int) + d3677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2610, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20676 p hg
    simpa only [d2610, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2610, d3677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20680 p hg
    simpa only [d2610, d3677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20682 (p : Pattern) (guard : d5850 p = 1) : d2611 p ≤ (0 : Int) + d3678 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d2611, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20579 p hg
    simpa only [d2611, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20683 (p : Pattern) (guard : d5850 p = 1) : d2545 p ≤ (0 : Int) + d34 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19929 p hg
    simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5850, d2545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20684 (p : Pattern) (guard : d5850 p = 1) : d2612 p ≤ (0 : Int) + d3679 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2612, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20683 p hg
    simpa only [d2612, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2612, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20586 p hg
    simpa only [d2612, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20685 (p : Pattern) (guard : d5850 p = 1) : d2613 p ≤ (0 : Int) + d3680 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2613, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20684 p hg
    simpa only [d2613, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2613, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20587 p hg
    simpa only [d2613, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20686 (p : Pattern) (guard : d5850 p = 1) : d2614 p ≤ (0 : Int) + d3681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2614, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20682 p hg
    simpa only [d2614, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2614, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20685 p hg
    simpa only [d2614, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20687 (p : Pattern) (guard : d5850 p = 1) : d2615 p ≤ (0 : Int) + d3682 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2615, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20686 p hg
    simpa only [d2615, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2615, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2615, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20688 (p : Pattern) (guard : d5850 p = 1) : d2616 p ≤ (0 : Int) + d3683 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2616, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20687 p hg
    simpa only [d2616, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2616, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2616, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20689 (p : Pattern) (guard : d5850 p = 1) : d2617 p ≤ (0 : Int) + d3684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2617, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20681 p hg
    simpa only [d2617, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2617, d3684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20688 p hg
    simpa only [d2617, d3684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20690 (p : Pattern) (guard : d5850 p = 1) : d2618 p ≤ (0 : Int) + d3685 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2618, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20669 p hg
    simpa only [d2618, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2618, d3685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20682 p hg
    simpa only [d2618, d3685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20691 (p : Pattern) (guard : d5850 p = 1) : d2619 p ≤ (0 : Int) + d3686 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2619, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d2619, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2619, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2619, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20692 (p : Pattern) (guard : d5850 p = 1) : d2620 p ≤ (0 : Int) + d3687 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2620, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20690 p hg
    simpa only [d2620, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2620, d3687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20691 p hg
    simpa only [d2620, d3687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20693 (p : Pattern) (guard : d5850 p = 1) : d2621 p ≤ (0 : Int) + d3688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2621, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d2621, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2621, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2621, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20694 (p : Pattern) (guard : d5850 p = 1) : d2622 p ≤ (0 : Int) + d3689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2622, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20693 p hg
    simpa only [d2622, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2622, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2622, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20695 (p : Pattern) (guard : d5850 p = 1) : d2623 p ≤ (0 : Int) + d3690 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2623, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20692 p hg
    simpa only [d2623, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2623, d3690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20694 p hg
    simpa only [d2623, d3690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20696 (p : Pattern) (guard : d5850 p = 1) : d2624 p ≤ (0 : Int) + d3691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2624, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20685 p hg
    simpa only [d2624, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2624, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2624, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20697 (p : Pattern) (guard : d5850 p = 1) : d2625 p ≤ (0 : Int) + d3692 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2625, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20696 p hg
    simpa only [d2625, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2625, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2625, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20698 (p : Pattern) (guard : d5850 p = 1) : d2626 p ≤ (0 : Int) + d3693 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2626, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20697 p hg
    simpa only [d2626, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2626, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2626, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20699 (p : Pattern) (guard : d5850 p = 1) : d2627 p ≤ (0 : Int) + d3694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2627, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20695 p hg
    simpa only [d2627, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2627, d3694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20698 p hg
    simpa only [d2627, d3694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20700 (p : Pattern) (guard : d5850 p = 1) : d2628 p ≤ (0 : Int) + d3695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2628, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20689 p hg
    simpa only [d2628, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2628, d3695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20699 p hg
    simpa only [d2628, d3695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20701 (p : Pattern) (guard : d5850 p = 1) : d2629 p ≤ (0 : Int) + d3696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2629, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20659 p hg
    simpa only [d2629, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2629, d3696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2629, d3696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20702 (p : Pattern) (guard : d5850 p = 1) : d2630 p ≤ (0 : Int) + d3697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2630, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2630, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2630, d3697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2630, d3697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20703 (p : Pattern) (guard : d5850 p = 1) : d2631 p ≤ (0 : Int) + d3698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2631, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20702 p hg
    simpa only [d2631, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2631, d3698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2631, d3698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20704 (p : Pattern) (guard : d5850 p = 1) : d2632 p ≤ (0 : Int) + d3699 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2632, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2632, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2632, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2632, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20705 (p : Pattern) (guard : d5850 p = 1) : d2633 p ≤ (0 : Int) + d3700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2633, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20703 p hg
    simpa only [d2633, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2633, d3700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20704 p hg
    simpa only [d2633, d3700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20706 (p : Pattern) (guard : d5850 p = 1) : d2634 p ≤ (0 : Int) + d3701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2634, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20704 p hg
    simpa only [d2634, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2634, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2634, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20707 (p : Pattern) (guard : d5850 p = 1) : d2635 p ≤ (0 : Int) + d3702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2635, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20705 p hg
    simpa only [d2635, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2635, d3702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20706 p hg
    simpa only [d2635, d3702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20708 (p : Pattern) (guard : d5850 p = 1) : d2636 p ≤ (0 : Int) + d3703 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2636, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20706 p hg
    simpa only [d2636, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2636, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2636, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20709 (p : Pattern) (guard : d5850 p = 1) : d2637 p ≤ (0 : Int) + d3704 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2637, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20707 p hg
    simpa only [d2637, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2637, d3704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20708 p hg
    simpa only [d2637, d3704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20710 (p : Pattern) (guard : d5850 p = 1) : d2638 p ≤ (0 : Int) + d3705 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2638, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20700 p hg
    simpa only [d2638, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2638, d3705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20709 p hg
    simpa only [d2638, d3705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20711 (p : Pattern) (guard : d5850 p = 1) : d2639 p ≤ (0 : Int) + d3706 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2639, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20701 p hg
    simpa only [d2639, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2639, d3706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20710 p hg
    simpa only [d2639, d3706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20712 (p : Pattern) (guard : d5850 p = 1) : d2640 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20530 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20713 (p : Pattern) (guard : d5850 p = 1) : d2641 p ≤ (0 : Int) + d3707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2641, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20712 p hg
    simpa only [d2641, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2641, d3707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20548 p hg
    simpa only [d2641, d3707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20714 (p : Pattern) (guard : d5850 p = 1) : d2642 p ≤ (0 : Int) + d3708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2642, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20713 p hg
    simpa only [d2642, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2642, d3708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20564 p hg
    simpa only [d2642, d3708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20715 (p : Pattern) (guard : d5850 p = 1) : d2643 p ≤ (0 : Int) + d3709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2643, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20714 p hg
    simpa only [d2643, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2643, d3709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20610 p hg
    simpa only [d2643, d3709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20716 (p : Pattern) (guard : d5850 p = 1) : d2644 p ≤ (0 : Int) + d3710 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2644, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20533 p hg
    simpa only [d2644, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2644, d3710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20628 p hg
    simpa only [d2644, d3710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20717 (p : Pattern) (guard : d5850 p = 1) : d2645 p ≤ (0 : Int) + d3711 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2645, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20716 p hg
    simpa only [d2645, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2645, d3711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20630 p hg
    simpa only [d2645, d3711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20718 (p : Pattern) (guard : d5850 p = 1) : d2646 p ≤ (0 : Int) + d3712 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2646, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20717 p hg
    simpa only [d2646, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2646, d3712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20645 p hg
    simpa only [d2646, d3712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20719 (p : Pattern) (guard : d5850 p = 1) : d2647 p ≤ (0 : Int) + d3713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2647, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20718 p hg
    simpa only [d2647, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2647, d3713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20657 p hg
    simpa only [d2647, d3713, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
