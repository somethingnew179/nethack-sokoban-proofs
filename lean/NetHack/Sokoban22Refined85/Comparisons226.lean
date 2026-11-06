/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons225
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31640 (p : Pattern) (guard : d5849 p = 1) : d3650 p ≤ (0 : Int) + d2250 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3650, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31628 p hg
    simpa only [d3650, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3650, d2250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3650, d2250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31641 (p : Pattern) (guard : d5849 p = 1) : d3651 p ≤ (0 : Int) + d2251 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3651, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31640 p hg
    simpa only [d3651, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3651, d2251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3651, d2251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31642 (p : Pattern) (guard : d5849 p = 1) : d3652 p ≤ (0 : Int) + d2252 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3652, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31639 p hg
    simpa only [d3652, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3652, d2252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31641 p hg
    simpa only [d3652, d2252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31643 (p : Pattern) (guard : d5849 p = 1) : d3653 p ≤ (0 : Int) + d2253 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3653, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31637 p hg
    simpa only [d3653, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3653, d2253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31642 p hg
    simpa only [d3653, d2253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31644 (p : Pattern) (guard : d5849 p = 1) : d3654 p ≤ (0 : Int) + d2254 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3654, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31632 p hg
    simpa only [d3654, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3654, d2254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31643 p hg
    simpa only [d3654, d2254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31645 (p : Pattern) (guard : d5849 p = 1) : d3655 p ≤ (0 : Int) + d2255 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3655, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31592 p hg
    simpa only [d3655, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3655, d2255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31644 p hg
    simpa only [d3655, d2255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31646 (p : Pattern) (guard : d0 p = 1) : d3656 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31647 (p : Pattern) (guard : d5849 p = 1) : d3657 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3657, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31554 p hg
    simpa only [d5849, d3657, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3657, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31646 p hg
    simpa only [d5849, d3657, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31648 (p : Pattern) (guard : d5849 p = 1) : d3658 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31532 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31647 p hg
    simpa only [d3658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31649 (p : Pattern) (guard : d5849 p = 1) : d3659 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3659, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3659, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3659, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3659, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31650 (p : Pattern) (guard : d5849 p = 1) : d3660 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3660, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31648 p hg
    simpa only [d3660, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3660, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31649 p hg
    simpa only [d3660, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31651 (p : Pattern) (guard : d0 p = 1) : d3662 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31652 (p : Pattern) (guard : d5849 p = 1) : d3663 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3663, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31554 p hg
    simpa only [d5849, d3663, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3663, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31651 p hg
    simpa only [d5849, d3663, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31653 (p : Pattern) (guard : d5849 p = 1) : d3664 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3664, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31652 p hg
    simpa only [d3664, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3664, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3664, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31654 (p : Pattern) (guard : d5849 p = 1) : d3665 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3665, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3665, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3665, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31653 p hg
    simpa only [d3665, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31655 (p : Pattern) (guard : d5849 p = 1) : d3666 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31650 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31654 p hg
    simpa only [d3666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31656 (p : Pattern) (guard : d5849 p = 1) : d3667 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3667, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31556 p hg
    simpa only [d3667, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3667, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3667, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31657 (p : Pattern) (guard : d5849 p = 1) : d3668 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3668, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31557 p hg
    simpa only [d3668, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3668, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31656 p hg
    simpa only [d3668, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31658 (p : Pattern) (guard : d5849 p = 1) : d3669 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3669, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31581 p hg
    simpa only [d3669, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3669, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3669, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31659 (p : Pattern) (guard : d5849 p = 1) : d3670 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3670, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31582 p hg
    simpa only [d3670, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3670, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31658 p hg
    simpa only [d3670, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31660 (p : Pattern) (guard : d5849 p = 1) : d3671 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3671, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31657 p hg
    simpa only [d3671, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3671, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d3671, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31661 (p : Pattern) (guard : d5849 p = 1) : d3672 p ≤ (0 : Int) + d2256 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31655 p hg
    simpa only [d3672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31660 p hg
    simpa only [d3672, d2256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31662 (p : Pattern) (guard : d5849 p = 1) : d3673 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3673, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31541 p hg
    simpa only [d3673, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3673, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3673, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31663 (p : Pattern) (guard : d5849 p = 1) : d3674 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3674, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31542 p hg
    simpa only [d3674, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3674, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31662 p hg
    simpa only [d3674, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31664 (p : Pattern) (guard : d5849 p = 1) : d3675 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3675, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d3675, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3675, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3675, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31665 (p : Pattern) (guard : d5849 p = 1) : d3676 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3676, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31660 p hg
    simpa only [d3676, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3676, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31664 p hg
    simpa only [d3676, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31666 (p : Pattern) (guard : d5849 p = 1) : d3677 p ≤ (0 : Int) + d2257 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3677, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31661 p hg
    simpa only [d3677, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3677, d2257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31665 p hg
    simpa only [d3677, d2257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31667 (p : Pattern) (guard : d5849 p = 1) : d3678 p ≤ (0 : Int) + d2232 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3678, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31633 p hg
    simpa only [d3678, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3678, d2232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31563 p hg
    simpa only [d3678, d2232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31668 (p : Pattern) (guard : d5847 p = 1) : d34 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26361 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14568 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31669 (p : Pattern) (guard : d5848 p = 1) : d34 p ≤ (0 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31668 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31670 (p : Pattern) (guard : d5849 p = 1) : d34 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31669 p hg
    simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5849, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31671 (p : Pattern) (guard : d5849 p = 1) : d3679 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31670 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31568 p hg
    simpa only [d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31672 (p : Pattern) (guard : d5849 p = 1) : d3680 p ≤ (0 : Int) + d2258 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3680, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31671 p hg
    simpa only [d3680, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3680, d2258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31569 p hg
    simpa only [d3680, d2258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31673 (p : Pattern) (guard : d5849 p = 1) : d3681 p ≤ (0 : Int) + d2259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3681, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31667 p hg
    simpa only [d3681, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3681, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31672 p hg
    simpa only [d3681, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31674 (p : Pattern) (guard : d5849 p = 1) : d3682 p ≤ (0 : Int) + d2260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3682, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31673 p hg
    simpa only [d3682, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3682, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3682, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31675 (p : Pattern) (guard : d5849 p = 1) : d3683 p ≤ (0 : Int) + d2261 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3683, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31674 p hg
    simpa only [d3683, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3683, d2261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3683, d2261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31676 (p : Pattern) (guard : d5849 p = 1) : d3684 p ≤ (0 : Int) + d2262 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3684, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31666 p hg
    simpa only [d3684, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3684, d2262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31675 p hg
    simpa only [d3684, d2262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31677 (p : Pattern) (guard : d5849 p = 1) : d3685 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3685, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31654 p hg
    simpa only [d3685, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3685, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31667 p hg
    simpa only [d3685, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31678 (p : Pattern) (guard : d5849 p = 1) : d3686 p ≤ (0 : Int) + d2234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3686, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d3686, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3686, d2234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d3686, d2234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31679 (p : Pattern) (guard : d5849 p = 1) : d3687 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3687, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31677 p hg
    simpa only [d3687, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3687, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31678 p hg
    simpa only [d3687, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31680 (p : Pattern) (guard : d5849 p = 1) : d3688 p ≤ (0 : Int) + d2239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3688, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31659 p hg
    simpa only [d3688, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3688, d2239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31623 p hg
    simpa only [d3688, d2239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31681 (p : Pattern) (guard : d5849 p = 1) : d3689 p ≤ (0 : Int) + d2242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3689, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31680 p hg
    simpa only [d3689, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3689, d2242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3689, d2242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31682 (p : Pattern) (guard : d5849 p = 1) : d3690 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3690, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31679 p hg
    simpa only [d3690, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3690, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31681 p hg
    simpa only [d3690, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31683 (p : Pattern) (guard : d5849 p = 1) : d3691 p ≤ (0 : Int) + d2266 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3691, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31672 p hg
    simpa only [d3691, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3691, d2266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3691, d2266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31684 (p : Pattern) (guard : d5849 p = 1) : d3692 p ≤ (0 : Int) + d2267 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3692, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31683 p hg
    simpa only [d3692, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3692, d2267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3692, d2267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31685 (p : Pattern) (guard : d5849 p = 1) : d3693 p ≤ (0 : Int) + d2268 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3693, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31684 p hg
    simpa only [d3693, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3693, d2268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3693, d2268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31686 (p : Pattern) (guard : d5849 p = 1) : d3694 p ≤ (0 : Int) + d2269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3694, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31682 p hg
    simpa only [d3694, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3694, d2269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31685 p hg
    simpa only [d3694, d2269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31687 (p : Pattern) (guard : d5849 p = 1) : d3695 p ≤ (0 : Int) + d2270 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3695, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31676 p hg
    simpa only [d3695, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3695, d2270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31686 p hg
    simpa only [d3695, d2270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31688 (p : Pattern) (guard : d5849 p = 1) : d3696 p ≤ (0 : Int) + d2271 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3696, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31645 p hg
    simpa only [d3696, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3696, d2271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3696, d2271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31689 (p : Pattern) (guard : d5849 p = 1) : d3658 p ≤ (0 : Int) + d2194 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3658, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31513 p hg
    simpa only [d3658, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3658, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31647 p hg
    simpa only [d3658, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31690 (p : Pattern) (guard : d5849 p = 1) : d3660 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3660, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31689 p hg
    simpa only [d3660, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3660, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31649 p hg
    simpa only [d3660, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31691 (p : Pattern) (guard : d5849 p = 1) : d3666 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3666, d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31690 p hg
    simpa only [d3666, d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3666, d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31654 p hg
    simpa only [d3666, d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31692 (p : Pattern) (guard : d5849 p = 1) : d3672 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3672, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31691 p hg
    simpa only [d3672, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3672, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31660 p hg
    simpa only [d3672, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31693 (p : Pattern) (guard : d5849 p = 1) : d3677 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3677, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31692 p hg
    simpa only [d3677, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3677, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31665 p hg
    simpa only [d3677, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31694 (p : Pattern) (guard : d5849 p = 1) : d3684 p ≤ (0 : Int) + d2275 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3684, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31693 p hg
    simpa only [d3684, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3684, d2275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31675 p hg
    simpa only [d3684, d2275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31695 (p : Pattern) (guard : d5849 p = 1) : d3695 p ≤ (0 : Int) + d2276 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3695, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31694 p hg
    simpa only [d3695, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3695, d2276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31686 p hg
    simpa only [d3695, d2276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31696 (p : Pattern) (guard : d5849 p = 1) : d3697 p ≤ (0 : Int) + d2277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3697, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31663 p hg
    simpa only [d3697, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3697, d2277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31629 p hg
    simpa only [d3697, d2277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31697 (p : Pattern) (guard : d5849 p = 1) : d3698 p ≤ (0 : Int) + d2278 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3698, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31696 p hg
    simpa only [d3698, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3698, d2278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3698, d2278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31698 (p : Pattern) (guard : d5849 p = 1) : d3699 p ≤ (0 : Int) + d2279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3699, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31630 p hg
    simpa only [d3699, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3699, d2279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3699, d2279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31699 (p : Pattern) (guard : d5849 p = 1) : d3700 p ≤ (0 : Int) + d2280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3700, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31697 p hg
    simpa only [d3700, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3700, d2280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31698 p hg
    simpa only [d3700, d2280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31700 (p : Pattern) (guard : d5849 p = 1) : d3701 p ≤ (0 : Int) + d2281 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3701, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31698 p hg
    simpa only [d3701, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3701, d2281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3701, d2281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31701 (p : Pattern) (guard : d5849 p = 1) : d3702 p ≤ (0 : Int) + d2282 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3702, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31699 p hg
    simpa only [d3702, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3702, d2282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31700 p hg
    simpa only [d3702, d2282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31702 (p : Pattern) (guard : d5849 p = 1) : d3703 p ≤ (0 : Int) + d2283 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3703, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31700 p hg
    simpa only [d3703, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3703, d2283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3703, d2283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31703 (p : Pattern) (guard : d5849 p = 1) : d3704 p ≤ (0 : Int) + d2284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3704, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31701 p hg
    simpa only [d3704, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3704, d2284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31702 p hg
    simpa only [d3704, d2284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31704 (p : Pattern) (guard : d5849 p = 1) : d3705 p ≤ (0 : Int) + d2285 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3705, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31695 p hg
    simpa only [d3705, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3705, d2285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31703 p hg
    simpa only [d3705, d2285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31705 (p : Pattern) (guard : d5849 p = 1) : d3706 p ≤ (0 : Int) + d2286 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3706, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31688 p hg
    simpa only [d3706, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3706, d2286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31704 p hg
    simpa only [d3706, d2286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31706 (p : Pattern) (guard : d5849 p = 1) : d3553 p ≤ (0 : Int) + d2287 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31510 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31534 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31707 (p : Pattern) (guard : d5849 p = 1) : d3707 p ≤ (0 : Int) + d2288 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3707, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31706 p hg
    simpa only [d3707, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3707, d2288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31535 p hg
    simpa only [d3707, d2288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31708 (p : Pattern) (guard : d5849 p = 1) : d3708 p ≤ (0 : Int) + d2289 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3708, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31707 p hg
    simpa only [d3708, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3708, d2289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31550 p hg
    simpa only [d3708, d2289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31709 (p : Pattern) (guard : d5849 p = 1) : d3709 p ≤ (0 : Int) + d2290 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3709, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31708 p hg
    simpa only [d3709, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3709, d2290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d3709, d2290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31710 (p : Pattern) (guard : d5849 p = 1) : d3710 p ≤ (0 : Int) + d2263 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3710, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31534 p hg
    simpa only [d3710, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3710, d2263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31611 p hg
    simpa only [d3710, d2263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31711 (p : Pattern) (guard : d5849 p = 1) : d3711 p ≤ (0 : Int) + d2264 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3711, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31710 p hg
    simpa only [d3711, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3711, d2264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31613 p hg
    simpa only [d3711, d2264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31712 (p : Pattern) (guard : d5849 p = 1) : d3712 p ≤ (0 : Int) + d2265 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3712, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31711 p hg
    simpa only [d3712, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3712, d2265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31631 p hg
    simpa only [d3712, d2265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31713 (p : Pattern) (guard : d5849 p = 1) : d3713 p ≤ (0 : Int) + d2291 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3713, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31712 p hg
    simpa only [d3713, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3713, d2291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31643 p hg
    simpa only [d3713, d2291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31714 (p : Pattern) (guard : d5849 p = 1) : d3714 p ≤ (0 : Int) + d2292 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3714, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31709 p hg
    simpa only [d3714, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3714, d2292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31713 p hg
    simpa only [d3714, d2292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31715 (p : Pattern) (guard : d5849 p = 1) : d3715 p ≤ (0 : Int) + d2293 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3715, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31714 p hg
    simpa only [d3715, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3715, d2293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3715, d2293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31716 (p : Pattern) (guard : d5849 p = 1) : d3716 p ≤ (0 : Int) + d2294 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3716, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3716, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3716, d2294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3716, d2294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31717 (p : Pattern) (guard : d5849 p = 1) : d3717 p ≤ (0 : Int) + d2295 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3717, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31715 p hg
    simpa only [d3717, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3717, d2295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31716 p hg
    simpa only [d3717, d2295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31718 (p : Pattern) (guard : d5849 p = 1) : d3718 p ≤ (0 : Int) + d2296 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3718, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31705 p hg
    simpa only [d3718, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3718, d2296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31717 p hg
    simpa only [d3718, d2296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31719 (p : Pattern) (guard : d5848 p = 1) : d3720 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29436 p hg
    simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31491 p hg
    simpa only [d5848, d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31720 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31721 (p : Pattern) (guard : d5849 p = 1) : d3721 p ≤ (0 : Int) + d2297 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3721, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31719 p hg
    simpa only [d5849, d3721, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3721, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31720 p hg
    simpa only [d5849, d3721, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31722 (p : Pattern) (guard : d5849 p = 1) : d3722 p ≤ (0 : Int) + d2298 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3722, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31721 p hg
    simpa only [d3722, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3722, d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31498 p hg
    simpa only [d3722, d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31723 (p : Pattern) (guard : d5849 p = 1) : d3723 p ≤ (0 : Int) + d2299 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3723, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31722 p hg
    simpa only [d3723, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3723, d2299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31504 p hg
    simpa only [d3723, d2299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31724 (p : Pattern) (guard : d5849 p = 1) : d3724 p ≤ (0 : Int) + d2300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3724, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31723 p hg
    simpa only [d3724, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3724, d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31515 p hg
    simpa only [d3724, d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31725 (p : Pattern) (guard : d5849 p = 1) : d3725 p ≤ (0 : Int) + d2301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3725, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31724 p hg
    simpa only [d3725, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3725, d2301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31535 p hg
    simpa only [d3725, d2301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31726 (p : Pattern) (guard : d5849 p = 1) : d3726 p ≤ (0 : Int) + d2302 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3726, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31725 p hg
    simpa only [d3726, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3726, d2302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31550 p hg
    simpa only [d3726, d2302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31727 (p : Pattern) (guard : d5849 p = 1) : d3727 p ≤ (0 : Int) + d2303 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3727, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31726 p hg
    simpa only [d3727, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3727, d2303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d3727, d2303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31728 (p : Pattern) (guard : d5849 p = 1) : d3710 p ≤ (0 : Int) + d2304 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3710, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31510 p hg
    simpa only [d3710, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3710, d2304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31611 p hg
    simpa only [d3710, d2304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31729 (p : Pattern) (guard : d5849 p = 1) : d3711 p ≤ (0 : Int) + d2305 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3711, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31728 p hg
    simpa only [d3711, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3711, d2305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31613 p hg
    simpa only [d3711, d2305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31730 (p : Pattern) (guard : d5849 p = 1) : d3712 p ≤ (0 : Int) + d2306 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3712, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31729 p hg
    simpa only [d3712, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3712, d2306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31631 p hg
    simpa only [d3712, d2306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31731 (p : Pattern) (guard : d5849 p = 1) : d3713 p ≤ (0 : Int) + d2307 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3713, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31730 p hg
    simpa only [d3713, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3713, d2307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31643 p hg
    simpa only [d3713, d2307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31732 (p : Pattern) (guard : d5849 p = 1) : d3728 p ≤ (0 : Int) + d2308 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3728, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31727 p hg
    simpa only [d3728, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3728, d2308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31731 p hg
    simpa only [d3728, d2308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31733 (p : Pattern) (guard : d5849 p = 1) : d3729 p ≤ (0 : Int) + d2309 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3729, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31732 p hg
    simpa only [d3729, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3729, d2309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3729, d2309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31734 (p : Pattern) (guard : d5849 p = 1) : d3705 p ≤ (0 : Int) + d2310 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3705, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3705, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3705, d2310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31703 p hg
    simpa only [d3705, d2310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31735 (p : Pattern) (guard : d5849 p = 1) : d3730 p ≤ (0 : Int) + d2311 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3730, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31733 p hg
    simpa only [d3730, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3730, d2311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31734 p hg
    simpa only [d3730, d2311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31736 (p : Pattern) (guard : d5849 p = 1) : d3553 p ≤ (0 : Int) + d2272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31515 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31534 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31737 (p : Pattern) (guard : d5849 p = 1) : d3707 p ≤ (0 : Int) + d2273 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3707, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31736 p hg
    simpa only [d3707, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3707, d2273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31535 p hg
    simpa only [d3707, d2273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31738 (p : Pattern) (guard : d5849 p = 1) : d3708 p ≤ (0 : Int) + d2274 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3708, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31737 p hg
    simpa only [d3708, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3708, d2274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31550 p hg
    simpa only [d3708, d2274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31739 (p : Pattern) (guard : d5849 p = 1) : d3709 p ≤ (0 : Int) + d2312 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3709, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31738 p hg
    simpa only [d3709, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3709, d2312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31591 p hg
    simpa only [d3709, d2312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31740 (p : Pattern) (guard : d5849 p = 1) : d3714 p ≤ (0 : Int) + d2313 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3714, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31739 p hg
    simpa only [d3714, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3714, d2313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31713 p hg
    simpa only [d3714, d2313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31741 (p : Pattern) (guard : d5849 p = 1) : d3715 p ≤ (0 : Int) + d2314 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3715, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31740 p hg
    simpa only [d3715, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3715, d2314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31687 p hg
    simpa only [d3715, d2314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31742 (p : Pattern) (guard : d5849 p = 1) : d3717 p ≤ (0 : Int) + d2315 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3717, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31741 p hg
    simpa only [d3717, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3717, d2315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31716 p hg
    simpa only [d3717, d2315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31743 (p : Pattern) (guard : d5849 p = 1) : d3731 p ≤ (0 : Int) + d2316 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3731, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31735 p hg
    simpa only [d3731, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3731, d2316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31742 p hg
    simpa only [d3731, d2316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31744 (p : Pattern) (guard : d5849 p = 1) : d3732 p ≤ (0 : Int) + d2317 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3732, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31718 p hg
    simpa only [d3732, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3732, d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31743 p hg
    simpa only [d3732, d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31745 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14648 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31746 (p : Pattern) (guard : d5848 p = 1) : d3734 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29463 p hg
    simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31745 p hg
    simpa only [d5848, d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31747 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31748 (p : Pattern) (guard : d5849 p = 1) : d3735 p ≤ (0 : Int) + d2318 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3735, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31746 p hg
    simpa only [d5849, d3735, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3735, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31747 p hg
    simpa only [d5849, d3735, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31749 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31750 (p : Pattern) (guard : d5847 p = 1) : d3736 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3736, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3736, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3736, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31749 p hg
    simpa only [d5847, d3736, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31751 (p : Pattern) (guard : d5848 p = 1) : d3737 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31750 p hg
    simpa only [d5848, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31752 (p : Pattern) (guard : d5849 p = 1) : d3738 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3738, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31751 p hg
    simpa only [d5849, d3738, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3738, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5849, d3738, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31753 (p : Pattern) (guard : d5849 p = 1) : d3739 p ≤ (0 : Int) + d2320 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3739, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31748 p hg
    simpa only [d3739, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3739, d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d3739, d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31754 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31755 (p : Pattern) (guard : d5847 p = 1) : d3740 p ≤ (0 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3740, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26431 p hg
    simpa only [d5847, d3740, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3740, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31754 p hg
    simpa only [d5847, d3740, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31756 (p : Pattern) (guard : d5848 p = 1) : d3741 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31755 p hg
    simpa only [d5848, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31757 (p : Pattern) (guard : d5849 p = 1) : d3742 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3742, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31756 p hg
    simpa only [d5849, d3742, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3742, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5849, d3742, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31758 (p : Pattern) (guard : d5849 p = 1) : d3743 p ≤ (0 : Int) + d2321 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3743, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31757 p hg
    simpa only [d3743, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3743, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d3743, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31759 (p : Pattern) (guard : d5849 p = 1) : d3744 p ≤ (0 : Int) + d2322 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3744, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31753 p hg
    simpa only [d3744, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3744, d2322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31758 p hg
    simpa only [d3744, d2322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31760 (p : Pattern) (guard : d5848 p = 1) : d102 p ≤ (0 : Int) + d103 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29466 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31745 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31761 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31762 (p : Pattern) (guard : d5849 p = 1) : d102 p ≤ (0 : Int) + d2323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31760 p hg
    simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31761 p hg
    simpa only [d5849, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31763 (p : Pattern) (guard : d5849 p = 1) : d3745 p ≤ (0 : Int) + d2324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3745, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31762 p hg
    simpa only [d3745, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3745, d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d3745, d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31764 (p : Pattern) (guard : d5849 p = 1) : d3746 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31763 p hg
    simpa only [d3746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31758 p hg
    simpa only [d3746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31765 (p : Pattern) (guard : d5849 p = 1) : d3747 p ≤ (0 : Int) + d2326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3747, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31759 p hg
    simpa only [d3747, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3747, d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31764 p hg
    simpa only [d3747, d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31766 (p : Pattern) (guard : d5849 p = 1) : d102 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31760 p hg
    simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5849, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31767 (p : Pattern) (guard : d5849 p = 1) : d3745 p ≤ (0 : Int) + d2319 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31766 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31768 (p : Pattern) (guard : d5849 p = 1) : d3746 p ≤ (0 : Int) + d2327 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31767 p hg
    simpa only [d3746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31758 p hg
    simpa only [d3746, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31769 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14656 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31770 (p : Pattern) (guard : d5848 p = 1) : d106 p ≤ (0 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31769 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31771 (p : Pattern) (guard : d5849 p = 1) : d106 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31770 p hg
    simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5849, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31772 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31773 (p : Pattern) (guard : d5847 p = 1) : d3748 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3748, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3748, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3748, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31772 p hg
    simpa only [d5847, d3748, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31774 (p : Pattern) (guard : d5848 p = 1) : d3749 p ≤ (0 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31773 p hg
    simpa only [d5848, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31775 (p : Pattern) (guard : d5849 p = 1) : d3750 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d3750, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31774 p hg
    simpa only [d5849, d3750, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d3750, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d5849, d3750, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31776 (p : Pattern) (guard : d5849 p = 1) : d3751 p ≤ (0 : Int) + d2328 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31771 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31775 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31777 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31778 (p : Pattern) (guard : d5847 p = 1) : d3752 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3752, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26437 p hg
    simpa only [d5847, d3752, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3752, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31777 p hg
    simpa only [d5847, d3752, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31779 (p : Pattern) (guard : d5848 p = 1) : d3753 p ≤ (0 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29487 p hg
    simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31778 p hg
    simpa only [d5848, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
