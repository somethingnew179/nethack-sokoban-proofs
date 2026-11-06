/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons224
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31500 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31501 (p : Pattern) (guard : d5847 p = 1) : d3547 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3547, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3547, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3547, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31500 p hg
    simpa only [d5847, d3547, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31502 (p : Pattern) (guard : d5848 p = 1) : d3548 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31501 p hg
    simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31503 (p : Pattern) (guard : d5849 p = 1) : d3549 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3549, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31502 p hg
    simpa only [d5849, d3549, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3549, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d5849, d3549, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31504 (p : Pattern) (guard : d5849 p = 1) : d3550 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3550, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31503 p hg
    simpa only [d3550, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3550, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3550, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31505 (p : Pattern) (guard : d5849 p = 1) : d3551 p ≤ (0 : Int) + d2188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3551, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31499 p hg
    simpa only [d3551, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3551, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3551, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31506 (p : Pattern) (guard : d5848 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31491 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31507 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31508 (p : Pattern) (guard : d5849 p = 1) : d13 p ≤ (0 : Int) + d2189 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31506 p hg
    simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31507 p hg
    simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31509 (p : Pattern) (guard : d5849 p = 1) : d3552 p ≤ (0 : Int) + d2190 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3552, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31508 p hg
    simpa only [d3552, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3552, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3552, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31510 (p : Pattern) (guard : d5849 p = 1) : d3553 p ≤ (0 : Int) + d2191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31509 p hg
    simpa only [d3553, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3553, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31511 (p : Pattern) (guard : d5849 p = 1) : d3554 p ≤ (0 : Int) + d2192 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3554, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31505 p hg
    simpa only [d3554, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3554, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31510 p hg
    simpa only [d3554, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31512 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31513 (p : Pattern) (guard : d5849 p = 1) : d13 p ≤ (0 : Int) + d2193 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31506 p hg
    simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31512 p hg
    simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31514 (p : Pattern) (guard : d5849 p = 1) : d3552 p ≤ (0 : Int) + d2194 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3552, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31513 p hg
    simpa only [d3552, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3552, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3552, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31515 (p : Pattern) (guard : d5849 p = 1) : d3553 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31514 p hg
    simpa only [d3553, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3553, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31516 (p : Pattern) (guard : d5847 p = 1) : d17 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14539 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31517 (p : Pattern) (guard : d5848 p = 1) : d17 p ≤ (0 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31516 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31518 (p : Pattern) (guard : d5849 p = 1) : d17 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31517 p hg
    simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31519 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31520 (p : Pattern) (guard : d5847 p = 1) : d3555 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3555, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3555, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3555, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31519 p hg
    simpa only [d5847, d3555, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31521 (p : Pattern) (guard : d5848 p = 1) : d3556 p ≤ (0 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31520 p hg
    simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31522 (p : Pattern) (guard : d5849 p = 1) : d3557 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3557, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31521 p hg
    simpa only [d5849, d3557, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3557, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d5849, d3557, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31523 (p : Pattern) (guard : d5849 p = 1) : d3558 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31518 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31522 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31524 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31525 (p : Pattern) (guard : d5847 p = 1) : d3559 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3559, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3559, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3559, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31524 p hg
    simpa only [d5847, d3559, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31526 (p : Pattern) (guard : d5848 p = 1) : d3560 p ≤ (0 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31525 p hg
    simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31527 (p : Pattern) (guard : d5849 p = 1) : d3561 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3561, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31526 p hg
    simpa only [d5849, d3561, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3561, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d5849, d3561, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31528 (p : Pattern) (guard : d5849 p = 1) : d3562 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3562, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31527 p hg
    simpa only [d3562, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3562, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3562, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31529 (p : Pattern) (guard : d5849 p = 1) : d3563 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3563, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31523 p hg
    simpa only [d3563, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3563, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31528 p hg
    simpa only [d3563, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31530 (p : Pattern) (guard : d5849 p = 1) : d3564 p ≤ (0 : Int) + d2199 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3564, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31515 p hg
    simpa only [d3564, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3564, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31529 p hg
    simpa only [d3564, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31531 (p : Pattern) (guard : d5849 p = 1) : d3565 p ≤ (0 : Int) + d2200 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3565, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31511 p hg
    simpa only [d3565, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3565, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31530 p hg
    simpa only [d3565, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31532 (p : Pattern) (guard : d5849 p = 1) : d13 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31506 p hg
    simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5849, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31533 (p : Pattern) (guard : d5849 p = 1) : d3552 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31532 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31534 (p : Pattern) (guard : d5849 p = 1) : d3553 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31533 p hg
    simpa only [d3553, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3553, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3553, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31535 (p : Pattern) (guard : d5849 p = 1) : d3564 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3564, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31534 p hg
    simpa only [d3564, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3564, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31529 p hg
    simpa only [d3564, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31536 (p : Pattern) (guard : d5847 p = 1) : d23 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14549 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31537 (p : Pattern) (guard : d5848 p = 1) : d23 p ≤ (0 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31536 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31538 (p : Pattern) (guard : d5849 p = 1) : d23 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31537 p hg
    simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5849, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31539 (p : Pattern) (guard : d5847 p = 1) : d356 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19893 p hg
    simpa only [d5847, d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31540 (p : Pattern) (guard : d5848 p = 1) : d3566 p ≤ (0 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31539 p hg
    simpa only [d5848, d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31541 (p : Pattern) (guard : d5849 p = 1) : d3567 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3567, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31540 p hg
    simpa only [d5849, d3567, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3567, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5849, d3567, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31542 (p : Pattern) (guard : d5849 p = 1) : d3568 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31538 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31541 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31543 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31544 (p : Pattern) (guard : d5847 p = 1) : d3569 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3569, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d5847, d3569, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3569, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31543 p hg
    simpa only [d5847, d3569, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31545 (p : Pattern) (guard : d5848 p = 1) : d3570 p ≤ (0 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31544 p hg
    simpa only [d5848, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31546 (p : Pattern) (guard : d5849 p = 1) : d3571 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3571, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31545 p hg
    simpa only [d5849, d3571, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3571, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d5849, d3571, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31547 (p : Pattern) (guard : d5849 p = 1) : d3572 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3572, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31546 p hg
    simpa only [d3572, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3572, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3572, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31548 (p : Pattern) (guard : d5849 p = 1) : d3573 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3573, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d3573, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3573, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31547 p hg
    simpa only [d3573, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31549 (p : Pattern) (guard : d5849 p = 1) : d3574 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3574, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31548 p hg
    simpa only [d3574, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3574, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3574, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31550 (p : Pattern) (guard : d5849 p = 1) : d3575 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3575, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31535 p hg
    simpa only [d3575, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3575, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31549 p hg
    simpa only [d3575, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31551 (p : Pattern) (guard : d5849 p = 1) : d3576 p ≤ (0 : Int) + d2208 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3576, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31531 p hg
    simpa only [d3576, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3576, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31550 p hg
    simpa only [d3576, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31552 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31553 (p : Pattern) (guard : d5847 p = 1) : d3577 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3577, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d5847, d3577, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3577, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31552 p hg
    simpa only [d5847, d3577, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31554 (p : Pattern) (guard : d5848 p = 1) : d3578 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31553 p hg
    simpa only [d5848, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31555 (p : Pattern) (guard : d0 p = 1) : d3580 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31556 (p : Pattern) (guard : d5849 p = 1) : d3581 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3581, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31554 p hg
    simpa only [d5849, d3581, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3581, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31555 p hg
    simpa only [d5849, d3581, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31557 (p : Pattern) (guard : d5849 p = 1) : d3582 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31532 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31556 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31558 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31559 (p : Pattern) (guard : d5847 p = 1) : d3583 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3583, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3583, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3583, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31558 p hg
    simpa only [d5847, d3583, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31560 (p : Pattern) (guard : d5848 p = 1) : d3584 p ≤ (0 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31559 p hg
    simpa only [d5848, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31561 (p : Pattern) (guard : d0 p = 1) : d3586 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31562 (p : Pattern) (guard : d5849 p = 1) : d3587 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3587, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31560 p hg
    simpa only [d5849, d3587, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3587, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31561 p hg
    simpa only [d5849, d3587, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31563 (p : Pattern) (guard : d5849 p = 1) : d3588 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3588, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31562 p hg
    simpa only [d3588, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3588, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3588, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31564 (p : Pattern) (guard : d5849 p = 1) : d3589 p ≤ (0 : Int) + d2211 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3589, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3589, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3589, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31563 p hg
    simpa only [d3589, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31565 (p : Pattern) (guard : d5847 p = 1) : d364 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d5847, d364, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20051 p hg
    simpa only [d5847, d364, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31566 (p : Pattern) (guard : d5848 p = 1) : d3590 p ≤ (0 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31565 p hg
    simpa only [d5848, d3590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31567 (p : Pattern) (guard : d0 p = 1) : d3592 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31568 (p : Pattern) (guard : d5849 p = 1) : d3593 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3593, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31566 p hg
    simpa only [d5849, d3593, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3593, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31567 p hg
    simpa only [d5849, d3593, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31569 (p : Pattern) (guard : d5849 p = 1) : d3594 p ≤ (0 : Int) + d2213 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3594, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31568 p hg
    simpa only [d3594, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3594, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3594, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31570 (p : Pattern) (guard : d5849 p = 1) : d3595 p ≤ (0 : Int) + d2214 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3595, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3595, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3595, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31569 p hg
    simpa only [d3595, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31571 (p : Pattern) (guard : d5849 p = 1) : d3596 p ≤ (0 : Int) + d2215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3596, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31564 p hg
    simpa only [d3596, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3596, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31570 p hg
    simpa only [d3596, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31572 (p : Pattern) (guard : d5847 p = 1) : d327 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d5847, d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31573 (p : Pattern) (guard : d5848 p = 1) : d3597 p ≤ (0 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31572 p hg
    simpa only [d5848, d3597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31574 (p : Pattern) (guard : d5849 p = 1) : d3598 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3598, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31573 p hg
    simpa only [d5849, d3598, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3598, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17139 p hg
    simpa only [d5849, d3598, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31575 (p : Pattern) (guard : d5849 p = 1) : d3599 p ≤ (0 : Int) + d2217 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3599, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31574 p hg
    simpa only [d3599, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3599, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3599, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31576 (p : Pattern) (guard : d5849 p = 1) : d3600 p ≤ (0 : Int) + d2218 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3600, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3600, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3600, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31575 p hg
    simpa only [d3600, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31577 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31578 (p : Pattern) (guard : d5847 p = 1) : d3601 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3601, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d5847, d3601, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3601, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31577 p hg
    simpa only [d5847, d3601, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31579 (p : Pattern) (guard : d5848 p = 1) : d3602 p ≤ (0 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31578 p hg
    simpa only [d5848, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31580 (p : Pattern) (guard : d0 p = 1) : d3603 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31581 (p : Pattern) (guard : d5849 p = 1) : d3604 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3604, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31579 p hg
    simpa only [d5849, d3604, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3604, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31580 p hg
    simpa only [d5849, d3604, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31582 (p : Pattern) (guard : d5849 p = 1) : d3605 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31518 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31581 p hg
    simpa only [d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31583 (p : Pattern) (guard : d5849 p = 1) : d3606 p ≤ (0 : Int) + d2219 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3606, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31582 p hg
    simpa only [d3606, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3606, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3606, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31584 (p : Pattern) (guard : d5849 p = 1) : d3607 p ≤ (0 : Int) + d2220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3607, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31576 p hg
    simpa only [d3607, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3607, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d3607, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31585 (p : Pattern) (guard : d5849 p = 1) : d3608 p ≤ (0 : Int) + d2221 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3608, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31571 p hg
    simpa only [d3608, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3608, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31584 p hg
    simpa only [d3608, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31586 (p : Pattern) (guard : d5849 p = 1) : d3609 p ≤ (0 : Int) + d2222 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3609, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3609, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3609, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3609, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31587 (p : Pattern) (guard : d5849 p = 1) : d3610 p ≤ (0 : Int) + d2223 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3610, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31586 p hg
    simpa only [d3610, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3610, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d3610, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31588 (p : Pattern) (guard : d5849 p = 1) : d3611 p ≤ (0 : Int) + d2224 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3611, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d3611, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3611, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3611, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31589 (p : Pattern) (guard : d5849 p = 1) : d3612 p ≤ (0 : Int) + d2225 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3612, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31588 p hg
    simpa only [d3612, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3612, d2225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3612, d2225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31590 (p : Pattern) (guard : d5849 p = 1) : d3613 p ≤ (0 : Int) + d2226 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3613, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31587 p hg
    simpa only [d3613, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3613, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31589 p hg
    simpa only [d3613, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31591 (p : Pattern) (guard : d5849 p = 1) : d3614 p ≤ (0 : Int) + d2227 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3614, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31585 p hg
    simpa only [d3614, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3614, d2227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31590 p hg
    simpa only [d3614, d2227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31592 (p : Pattern) (guard : d5849 p = 1) : d3615 p ≤ (0 : Int) + d2228 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3615, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31551 p hg
    simpa only [d3615, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3615, d2228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d3615, d2228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31593 (p : Pattern) (guard : d5848 p = 1) : d3617 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29318 p hg
    simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31491 p hg
    simpa only [d5848, d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31594 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d357 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31595 (p : Pattern) (guard : d5849 p = 1) : d3618 p ≤ (0 : Int) + d2229 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3618, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31593 p hg
    simpa only [d5849, d3618, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3618, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31594 p hg
    simpa only [d5849, d3618, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31596 (p : Pattern) (guard : d5849 p = 1) : d3619 p ≤ (0 : Int) + d2230 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3619, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31595 p hg
    simpa only [d3619, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3619, d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3619, d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31597 (p : Pattern) (guard : d5849 p = 1) : d3620 p ≤ (0 : Int) + d2231 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3620, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31596 p hg
    simpa only [d3620, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3620, d2231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3620, d2231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31598 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14560 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31599 (p : Pattern) (guard : d5848 p = 1) : d30 p ≤ (0 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31598 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31600 (p : Pattern) (guard : d5849 p = 1) : d30 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31599 p hg
    simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5849, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31601 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31602 (p : Pattern) (guard : d5847 p = 1) : d3585 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3585, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3585, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3585, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31601 p hg
    simpa only [d5847, d3585, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31603 (p : Pattern) (guard : d5848 p = 1) : d3621 p ≤ (0 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31602 p hg
    simpa only [d5848, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31604 (p : Pattern) (guard : d5849 p = 1) : d3622 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3622, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31603 p hg
    simpa only [d5849, d3622, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3622, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d5849, d3622, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31605 (p : Pattern) (guard : d5849 p = 1) : d3623 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31600 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31604 p hg
    simpa only [d3623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31606 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31607 (p : Pattern) (guard : d5847 p = 1) : d3624 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3624, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26355 p hg
    simpa only [d5847, d3624, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3624, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31606 p hg
    simpa only [d5847, d3624, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31608 (p : Pattern) (guard : d5848 p = 1) : d3625 p ≤ (0 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31607 p hg
    simpa only [d5848, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31609 (p : Pattern) (guard : d5849 p = 1) : d3626 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3626, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31608 p hg
    simpa only [d5849, d3626, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3626, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d5849, d3626, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31610 (p : Pattern) (guard : d5849 p = 1) : d3627 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3627, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31609 p hg
    simpa only [d3627, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3627, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3627, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31611 (p : Pattern) (guard : d5849 p = 1) : d3628 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3628, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31605 p hg
    simpa only [d3628, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3628, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31610 p hg
    simpa only [d3628, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31612 (p : Pattern) (guard : d5849 p = 1) : d3629 p ≤ (0 : Int) + d2233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3629, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31597 p hg
    simpa only [d3629, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3629, d2233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31611 p hg
    simpa only [d3629, d2233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31613 (p : Pattern) (guard : d5849 p = 1) : d3630 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3630, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31529 p hg
    simpa only [d3630, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3630, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31548 p hg
    simpa only [d3630, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31614 (p : Pattern) (guard : d5849 p = 1) : d3631 p ≤ (0 : Int) + d2235 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3631, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31612 p hg
    simpa only [d3631, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3631, d2235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31613 p hg
    simpa only [d3631, d2235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31615 (p : Pattern) (guard : d5847 p = 1) : d57 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14599 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31616 (p : Pattern) (guard : d5848 p = 1) : d57 p ≤ (0 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31615 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31617 (p : Pattern) (guard : d5849 p = 1) : d57 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31616 p hg
    simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5849, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31618 (p : Pattern) (guard : d5847 p = 1) : d329 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d5847, d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19996 p hg
    simpa only [d5847, d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31619 (p : Pattern) (guard : d5848 p = 1) : d3632 p ≤ (0 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31618 p hg
    simpa only [d5848, d3632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31620 (p : Pattern) (guard : d5849 p = 1) : d3633 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3633, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31619 p hg
    simpa only [d5849, d3633, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3633, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17174 p hg
    simpa only [d5849, d3633, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31621 (p : Pattern) (guard : d5849 p = 1) : d3634 p ≤ (0 : Int) + d2236 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31617 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31620 p hg
    simpa only [d3634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31622 (p : Pattern) (guard : d5849 p = 1) : d3635 p ≤ (0 : Int) + d2237 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3635, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31620 p hg
    simpa only [d3635, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3635, d2237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3635, d2237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31623 (p : Pattern) (guard : d5849 p = 1) : d3636 p ≤ (0 : Int) + d2238 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3636, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31621 p hg
    simpa only [d3636, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3636, d2238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31622 p hg
    simpa only [d3636, d2238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31624 (p : Pattern) (guard : d5849 p = 1) : d3637 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3637, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31529 p hg
    simpa only [d3637, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3637, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3637, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31625 (p : Pattern) (guard : d5847 p = 1) : d39 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14577 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31626 (p : Pattern) (guard : d5848 p = 1) : d39 p ≤ (0 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31625 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31627 (p : Pattern) (guard : d5849 p = 1) : d39 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31626 p hg
    simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5849, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31628 (p : Pattern) (guard : d5849 p = 1) : d3638 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31627 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31574 p hg
    simpa only [d3638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31629 (p : Pattern) (guard : d5849 p = 1) : d3639 p ≤ (0 : Int) + d2240 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3639, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31628 p hg
    simpa only [d3639, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3639, d2240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31575 p hg
    simpa only [d3639, d2240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31630 (p : Pattern) (guard : d5849 p = 1) : d3640 p ≤ (0 : Int) + d2241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3640, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d3640, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3640, d2241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3640, d2241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31631 (p : Pattern) (guard : d5849 p = 1) : d3641 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3641, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31624 p hg
    simpa only [d3641, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3641, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3641, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31632 (p : Pattern) (guard : d5849 p = 1) : d3642 p ≤ (0 : Int) + d2243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3642, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31614 p hg
    simpa only [d3642, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3642, d2243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31631 p hg
    simpa only [d3642, d2243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31633 (p : Pattern) (guard : d5849 p = 1) : d3643 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31600 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31562 p hg
    simpa only [d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31634 (p : Pattern) (guard : d5849 p = 1) : d3644 p ≤ (0 : Int) + d2244 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3644, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d3644, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3644, d2244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3644, d2244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31635 (p : Pattern) (guard : d5849 p = 1) : d3645 p ≤ (0 : Int) + d2245 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3645, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31570 p hg
    simpa only [d3645, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3645, d2245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31634 p hg
    simpa only [d3645, d2245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31636 (p : Pattern) (guard : d5849 p = 1) : d3646 p ≤ (0 : Int) + d2246 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3646, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d3646, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3646, d2246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31588 p hg
    simpa only [d3646, d2246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31637 (p : Pattern) (guard : d5849 p = 1) : d3647 p ≤ (0 : Int) + d2247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3647, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31635 p hg
    simpa only [d3647, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3647, d2247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31636 p hg
    simpa only [d3647, d2247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31638 (p : Pattern) (guard : d5849 p = 1) : d3648 p ≤ (0 : Int) + d2248 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3648, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31621 p hg
    simpa only [d3648, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3648, d2248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3648, d2248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31639 (p : Pattern) (guard : d5849 p = 1) : d3649 p ≤ (0 : Int) + d2249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3649, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31583 p hg
    simpa only [d3649, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3649, d2249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31638 p hg
    simpa only [d3649, d2249, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
