/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons139
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19600 (p : Pattern) (guard : d5540 p = 1) : d2321 p ≤ (0 : Int) + d5656 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2321, d5656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19599 p hg
    simpa only [d2321, d5656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2321, d5656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2321, d5656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19601 (p : Pattern) (guard : d5540 p = 1) : d2322 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2322, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19597 p hg
    simpa only [d2322, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2322, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19600 p hg
    simpa only [d2322, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19602 (p : Pattern) (guard : d5540 p = 1) : d2323 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18121 p hg
    simpa only [d5540, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19603 (p : Pattern) (guard : d5540 p = 1) : d2324 p ≤ (0 : Int) + d5654 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2324, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19602 p hg
    simpa only [d2324, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2324, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d2324, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19604 (p : Pattern) (guard : d5540 p = 1) : d2325 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2325, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19603 p hg
    simpa only [d2325, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2325, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19600 p hg
    simpa only [d2325, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19605 (p : Pattern) (guard : d5540 p = 1) : d2326 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19601 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19604 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19606 (p : Pattern) (guard : d5540 p = 1) : d2319 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d5540, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19607 (p : Pattern) (guard : d5540 p = 1) : d2319 p ≤ (0 : Int) + d5654 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19606 p hg
    simpa only [d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19608 (p : Pattern) (guard : d5540 p = 1) : d2327 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2327, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d2327, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2327, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19600 p hg
    simpa only [d2327, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19609 (p : Pattern) (guard : d5501 p = 1) : d107 p ≤ (0 : Int) + d107 p := by
  omega
theorem compare19610 (p : Pattern) (guard : d5540 p = 1) : d2328 p ≤ (0 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19609 p hg
    simpa only [d5540, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d5540, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19611 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1964 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19612 (p : Pattern) (guard : d5540 p = 1) : d2328 p ≤ (0 : Int) + d5658 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2328, d5658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19609 p hg
    simpa only [d5540, d2328, d5658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2328, d5658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19611 p hg
    simpa only [d5540, d2328, d5658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19613 (p : Pattern) (guard : d5540 p = 1) : d2328 p ≤ (0 : Int) + d5659 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19610 p hg
    simpa only [d5659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19612 p hg
    simpa only [d5659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19614 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19615 (p : Pattern) (guard : d5540 p = 1) : d2328 p ≤ (0 : Int) + d5660 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2328, d5660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19609 p hg
    simpa only [d5540, d2328, d5660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2328, d5660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19614 p hg
    simpa only [d5540, d2328, d5660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19616 (p : Pattern) (guard : d5540 p = 1) : d2329 p ≤ (0 : Int) + d5661 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2329, d5661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19615 p hg
    simpa only [d2329, d5661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2329, d5661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2329, d5661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19617 (p : Pattern) (guard : d5540 p = 1) : d2330 p ≤ (0 : Int) + d5662 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2330, d5662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19613 p hg
    simpa only [d2330, d5662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2330, d5662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19616 p hg
    simpa only [d2330, d5662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19618 (p : Pattern) (guard : d5540 p = 1) : d2331 p ≤ (0 : Int) + d5663 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2331, d5663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19608 p hg
    simpa only [d2331, d5663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2331, d5663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19617 p hg
    simpa only [d2331, d5663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19619 (p : Pattern) (guard : d5540 p = 1) : d2332 p ≤ (0 : Int) + d5664 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2332, d5664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19605 p hg
    simpa only [d2332, d5664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2332, d5664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19618 p hg
    simpa only [d2332, d5664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19620 (p : Pattern) (guard : d5540 p = 1) : d2333 p ≤ (0 : Int) + d5665 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2333, d5665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d2333, d5665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2333, d5665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2333, d5665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19621 (p : Pattern) (guard : d5540 p = 1) : d2334 p ≤ (0 : Int) + d5666 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2334, d5666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19618 p hg
    simpa only [d2334, d5666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2334, d5666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19620 p hg
    simpa only [d2334, d5666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19622 (p : Pattern) (guard : d5540 p = 1) : d2335 p ≤ (0 : Int) + d5667 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2335, d5667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19619 p hg
    simpa only [d2335, d5667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2335, d5667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19621 p hg
    simpa only [d2335, d5667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19623 (p : Pattern) (guard : d5501 p = 1) : d116 p ≤ (0 : Int) + d116 p := by
  omega
theorem compare19624 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19625 (p : Pattern) (guard : d5540 p = 1) : d2336 p ≤ (0 : Int) + d5668 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2336, d5668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19623 p hg
    simpa only [d5540, d2336, d5668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2336, d5668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19624 p hg
    simpa only [d5540, d2336, d5668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19626 (p : Pattern) (guard : d5540 p = 1) : d2337 p ≤ (0 : Int) + d5669 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2337, d5669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19625 p hg
    simpa only [d2337, d5669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2337, d5669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2337, d5669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19627 (p : Pattern) (guard : d5540 p = 1) : d2338 p ≤ (0 : Int) + d5670 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2338, d5670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d2338, d5670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2338, d5670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19626 p hg
    simpa only [d2338, d5670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19628 (p : Pattern) (guard : d5501 p = 1) : d120 p ≤ (0 : Int) + d120 p := by
  omega
theorem compare19629 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1903 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19630 (p : Pattern) (guard : d5540 p = 1) : d2339 p ≤ (0 : Int) + d5671 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2339, d5671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19628 p hg
    simpa only [d5540, d2339, d5671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2339, d5671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19629 p hg
    simpa only [d5540, d2339, d5671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19631 (p : Pattern) (guard : d5540 p = 1) : d2340 p ≤ (0 : Int) + d5672 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2340, d5672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19630 p hg
    simpa only [d2340, d5672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2340, d5672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2340, d5672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19632 (p : Pattern) (guard : d5540 p = 1) : d2341 p ≤ (0 : Int) + d5673 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2341, d5673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d2341, d5673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2341, d5673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19631 p hg
    simpa only [d2341, d5673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19633 (p : Pattern) (guard : d5540 p = 1) : d2342 p ≤ (0 : Int) + d5674 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2342, d5674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19627 p hg
    simpa only [d2342, d5674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2342, d5674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19632 p hg
    simpa only [d2342, d5674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19634 (p : Pattern) (guard : d5540 p = 1) : d2343 p ≤ (0 : Int) + d5675 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2343, d5675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d2343, d5675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2343, d5675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2343, d5675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19635 (p : Pattern) (guard : d5540 p = 1) : d2344 p ≤ (0 : Int) + d5676 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2344, d5676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19613 p hg
    simpa only [d2344, d5676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2344, d5676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2344, d5676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19636 (p : Pattern) (guard : d5540 p = 1) : d2345 p ≤ (0 : Int) + d5677 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2345, d5677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19634 p hg
    simpa only [d2345, d5677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2345, d5677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d2345, d5677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19637 (p : Pattern) (guard : d5540 p = 1) : d2346 p ≤ (0 : Int) + d5678 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2346, d5678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19633 p hg
    simpa only [d2346, d5678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2346, d5678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19636 p hg
    simpa only [d2346, d5678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19638 (p : Pattern) (guard : d5540 p = 1) : d2347 p ≤ (0 : Int) + d5679 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2347, d5679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19501 p hg
    simpa only [d2347, d5679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2347, d5679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2347, d5679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19639 (p : Pattern) (guard : d5540 p = 1) : d2348 p ≤ (0 : Int) + d5680 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2348, d5680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19636 p hg
    simpa only [d2348, d5680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2348, d5680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19638 p hg
    simpa only [d2348, d5680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19640 (p : Pattern) (guard : d5540 p = 1) : d2349 p ≤ (0 : Int) + d5681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2349, d5681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19637 p hg
    simpa only [d2349, d5681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2349, d5681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19639 p hg
    simpa only [d2349, d5681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19641 (p : Pattern) (guard : d5540 p = 1) : d2350 p ≤ (0 : Int) + d5682 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2350, d5682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19622 p hg
    simpa only [d2350, d5682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2350, d5682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19640 p hg
    simpa only [d2350, d5682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19642 (p : Pattern) (guard : d5540 p = 1) : d2351 p ≤ (0 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19593 p hg
    simpa only [d5540, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18150 p hg
    simpa only [d5540, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19643 (p : Pattern) (guard : d5540 p = 1) : d2352 p ≤ (0 : Int) + d5654 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2352, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19642 p hg
    simpa only [d2352, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2352, d5654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d2352, d5654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19644 (p : Pattern) (guard : d5540 p = 1) : d2353 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2353, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19643 p hg
    simpa only [d2353, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2353, d5657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19600 p hg
    simpa only [d2353, d5657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19645 (p : Pattern) (guard : d5540 p = 1) : d2336 p ≤ (0 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19623 p hg
    simpa only [d5540, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d5540, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19646 (p : Pattern) (guard : d5540 p = 1) : d2336 p ≤ (0 : Int) + d5683 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19645 p hg
    simpa only [d5683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19625 p hg
    simpa only [d5683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19647 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19648 (p : Pattern) (guard : d5540 p = 1) : d2336 p ≤ (0 : Int) + d5684 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2336, d5684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19623 p hg
    simpa only [d5540, d2336, d5684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2336, d5684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19647 p hg
    simpa only [d5540, d2336, d5684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19649 (p : Pattern) (guard : d5540 p = 1) : d2337 p ≤ (0 : Int) + d5685 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2337, d5685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19648 p hg
    simpa only [d2337, d5685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2337, d5685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2337, d5685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19650 (p : Pattern) (guard : d5540 p = 1) : d2354 p ≤ (0 : Int) + d5686 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2354, d5686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19646 p hg
    simpa only [d2354, d5686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2354, d5686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19649 p hg
    simpa only [d2354, d5686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19651 (p : Pattern) (guard : d5540 p = 1) : d2355 p ≤ (0 : Int) + d5687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2355, d5687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19644 p hg
    simpa only [d2355, d5687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2355, d5687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19650 p hg
    simpa only [d2355, d5687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19652 (p : Pattern) (guard : d5540 p = 1) : d2356 p ≤ (0 : Int) + d5688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2356, d5688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19617 p hg
    simpa only [d2356, d5688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2356, d5688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d2356, d5688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19653 (p : Pattern) (guard : d5540 p = 1) : d2357 p ≤ (0 : Int) + d5689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2357, d5689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19651 p hg
    simpa only [d2357, d5689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2357, d5689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19652 p hg
    simpa only [d2357, d5689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19654 (p : Pattern) (guard : d5540 p = 1) : d2358 p ≤ (0 : Int) + d5690 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2358, d5690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19617 p hg
    simpa only [d2358, d5690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2358, d5690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2358, d5690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19655 (p : Pattern) (guard : d5540 p = 1) : d2359 p ≤ (0 : Int) + d5691 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2359, d5691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19654 p hg
    simpa only [d2359, d5691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2359, d5691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2359, d5691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19656 (p : Pattern) (guard : d5540 p = 1) : d2360 p ≤ (0 : Int) + d5692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2360, d5692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19653 p hg
    simpa only [d2360, d5692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2360, d5692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19655 p hg
    simpa only [d2360, d5692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19657 (p : Pattern) (guard : d5540 p = 1) : d2361 p ≤ (0 : Int) + d5693 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2361, d5693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19646 p hg
    simpa only [d2361, d5693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2361, d5693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2361, d5693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19658 (p : Pattern) (guard : d5540 p = 1) : d2362 p ≤ (0 : Int) + d5694 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2362, d5694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19632 p hg
    simpa only [d2362, d5694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2362, d5694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19657 p hg
    simpa only [d2362, d5694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19659 (p : Pattern) (guard : d5540 p = 1) : d2363 p ≤ (0 : Int) + d5695 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2363, d5695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d2363, d5695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2363, d5695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19501 p hg
    simpa only [d2363, d5695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19660 (p : Pattern) (guard : d5540 p = 1) : d2364 p ≤ (0 : Int) + d5696 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2364, d5696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19658 p hg
    simpa only [d2364, d5696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2364, d5696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19659 p hg
    simpa only [d2364, d5696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19661 (p : Pattern) (guard : d5540 p = 1) : d2365 p ≤ (0 : Int) + d5697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2365, d5697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d2365, d5697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2365, d5697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d2365, d5697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19662 (p : Pattern) (guard : d5540 p = 1) : d2366 p ≤ (0 : Int) + d5698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2366, d5698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19661 p hg
    simpa only [d2366, d5698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2366, d5698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2366, d5698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19663 (p : Pattern) (guard : d5540 p = 1) : d2367 p ≤ (0 : Int) + d5699 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2367, d5699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19660 p hg
    simpa only [d2367, d5699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2367, d5699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19662 p hg
    simpa only [d2367, d5699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19664 (p : Pattern) (guard : d5540 p = 1) : d2368 p ≤ (0 : Int) + d5700 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2368, d5700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19656 p hg
    simpa only [d2368, d5700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2368, d5700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19663 p hg
    simpa only [d2368, d5700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19665 (p : Pattern) (guard : d5540 p = 1) : d2369 p ≤ (0 : Int) + d5701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2369, d5701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19641 p hg
    simpa only [d2369, d5701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2369, d5701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19664 p hg
    simpa only [d2369, d5701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19666 (p : Pattern) (guard : d5540 p = 1) : d2321 p ≤ (0 : Int) + d5702 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2321, d5702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19596 p hg
    simpa only [d2321, d5702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2321, d5702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2321, d5702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19667 (p : Pattern) (guard : d5540 p = 1) : d2327 p ≤ (0 : Int) + d5703 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2327, d5703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19607 p hg
    simpa only [d2327, d5703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2327, d5703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19666 p hg
    simpa only [d2327, d5703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19668 (p : Pattern) (guard : d5540 p = 1) : d2329 p ≤ (0 : Int) + d5704 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2329, d5704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19612 p hg
    simpa only [d2329, d5704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2329, d5704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2329, d5704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19669 (p : Pattern) (guard : d5540 p = 1) : d2330 p ≤ (0 : Int) + d5705 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2330, d5705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19613 p hg
    simpa only [d2330, d5705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2330, d5705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19668 p hg
    simpa only [d2330, d5705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19670 (p : Pattern) (guard : d5540 p = 1) : d2331 p ≤ (0 : Int) + d5706 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2331, d5706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2331, d5706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2331, d5706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d2331, d5706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19671 (p : Pattern) (guard : d5540 p = 1) : d2370 p ≤ (0 : Int) + d5707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2370, d5707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2370, d5707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2370, d5707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19670 p hg
    simpa only [d2370, d5707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19672 (p : Pattern) (guard : d5540 p = 1) : d2334 p ≤ (0 : Int) + d5708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2334, d5708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19670 p hg
    simpa only [d2334, d5708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2334, d5708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19620 p hg
    simpa only [d2334, d5708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19673 (p : Pattern) (guard : d5540 p = 1) : d2371 p ≤ (0 : Int) + d5709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2371, d5709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19671 p hg
    simpa only [d2371, d5709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2371, d5709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19672 p hg
    simpa only [d2371, d5709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19674 (p : Pattern) (guard : d5540 p = 1) : d2354 p ≤ (0 : Int) + d5710 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2354, d5710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19646 p hg
    simpa only [d2354, d5710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2354, d5710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19626 p hg
    simpa only [d2354, d5710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19675 (p : Pattern) (guard : d5540 p = 1) : d2339 p ≤ (0 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19628 p hg
    simpa only [d5540, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d5540, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19676 (p : Pattern) (guard : d5540 p = 1) : d2339 p ≤ (0 : Int) + d5711 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19675 p hg
    simpa only [d5711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19630 p hg
    simpa only [d5711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19677 (p : Pattern) (guard : d5540 p = 1) : d2372 p ≤ (0 : Int) + d5712 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2372, d5712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19676 p hg
    simpa only [d2372, d5712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2372, d5712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19631 p hg
    simpa only [d2372, d5712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19678 (p : Pattern) (guard : d5540 p = 1) : d2373 p ≤ (0 : Int) + d5713 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2373, d5713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2373, d5713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2373, d5713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19677 p hg
    simpa only [d2373, d5713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19679 (p : Pattern) (guard : d5540 p = 1) : d2374 p ≤ (0 : Int) + d5714 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2374, d5714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19678 p hg
    simpa only [d2374, d5714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2374, d5714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2374, d5714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19680 (p : Pattern) (guard : d5540 p = 1) : d2375 p ≤ (0 : Int) + d5715 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2375, d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19679 p hg
    simpa only [d2375, d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2375, d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2375, d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19681 (p : Pattern) (guard : d5540 p = 1) : d2376 p ≤ (0 : Int) + d5716 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2376, d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19673 p hg
    simpa only [d2376, d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2376, d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19680 p hg
    simpa only [d2376, d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19682 (p : Pattern) (guard : d5540 p = 1) : d2377 p ≤ (0 : Int) + d5717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2377, d5717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2377, d5717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2377, d5717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2377, d5717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19683 (p : Pattern) (guard : d5540 p = 1) : d2356 p ≤ (0 : Int) + d5718 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2356, d5718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d2356, d5718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2356, d5718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d2356, d5718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19684 (p : Pattern) (guard : d5540 p = 1) : d2378 p ≤ (0 : Int) + d5719 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2378, d5719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19682 p hg
    simpa only [d2378, d5719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2378, d5719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19683 p hg
    simpa only [d2378, d5719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19685 (p : Pattern) (guard : d5540 p = 1) : d2358 p ≤ (0 : Int) + d5720 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2358, d5720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d2358, d5720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2358, d5720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2358, d5720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19686 (p : Pattern) (guard : d5540 p = 1) : d2359 p ≤ (0 : Int) + d5721 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2359, d5721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19685 p hg
    simpa only [d2359, d5721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2359, d5721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2359, d5721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19687 (p : Pattern) (guard : d5540 p = 1) : d2379 p ≤ (0 : Int) + d5722 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2379, d5722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19684 p hg
    simpa only [d2379, d5722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2379, d5722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19686 p hg
    simpa only [d2379, d5722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19688 (p : Pattern) (guard : d5540 p = 1) : d2380 p ≤ (0 : Int) + d5723 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2380, d5723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19677 p hg
    simpa only [d2380, d5723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2380, d5723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2380, d5723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19689 (p : Pattern) (guard : d5540 p = 1) : d2381 p ≤ (0 : Int) + d5724 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2381, d5724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19688 p hg
    simpa only [d2381, d5724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2381, d5724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2381, d5724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19690 (p : Pattern) (guard : d5540 p = 1) : d2382 p ≤ (0 : Int) + d5725 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2382, d5725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19689 p hg
    simpa only [d2382, d5725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2382, d5725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2382, d5725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19691 (p : Pattern) (guard : d5540 p = 1) : d2383 p ≤ (0 : Int) + d5726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2383, d5726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19687 p hg
    simpa only [d2383, d5726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2383, d5726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19690 p hg
    simpa only [d2383, d5726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19692 (p : Pattern) (guard : d5540 p = 1) : d2384 p ≤ (0 : Int) + d5727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2384, d5727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19681 p hg
    simpa only [d2384, d5727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2384, d5727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19691 p hg
    simpa only [d2384, d5727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19693 (p : Pattern) (guard : d5540 p = 1) : d2385 p ≤ (0 : Int) + d5728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2385, d5728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19665 p hg
    simpa only [d2385, d5728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2385, d5728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19692 p hg
    simpa only [d2385, d5728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19694 (p : Pattern) (guard : d5540 p = 1) : d2386 p ≤ (0 : Int) + d5729 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2386, d5729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19620 p hg
    simpa only [d2386, d5729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2386, d5729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2386, d5729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19695 (p : Pattern) (guard : d5540 p = 1) : d2387 p ≤ (0 : Int) + d5730 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2387, d5730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19694 p hg
    simpa only [d2387, d5730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2387, d5730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2387, d5730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19696 (p : Pattern) (guard : d5540 p = 1) : d2388 p ≤ (0 : Int) + d5731 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2388, d5731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19695 p hg
    simpa only [d2388, d5731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2388, d5731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2388, d5731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19697 (p : Pattern) (guard : d5540 p = 1) : d2389 p ≤ (0 : Int) + d5732 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2389, d5732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19696 p hg
    simpa only [d2389, d5732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2389, d5732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2389, d5732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19698 (p : Pattern) (guard : d5540 p = 1) : d2390 p ≤ (0 : Int) + d5733 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2390, d5733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19692 p hg
    simpa only [d2390, d5733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2390, d5733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19697 p hg
    simpa only [d2390, d5733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19699 (p : Pattern) (guard : d5540 p = 1) : d2391 p ≤ (0 : Int) + d5734 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2391, d5734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19693 p hg
    simpa only [d2391, d5734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2391, d5734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19698 p hg
    simpa only [d2391, d5734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19700 (p : Pattern) (guard : d5540 p = 1) : d2392 p ≤ (0 : Int) + d5657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19604 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19608 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19701 (p : Pattern) (guard : d5540 p = 1) : d2393 p ≤ (0 : Int) + d5664 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2393, d5664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19700 p hg
    simpa only [d2393, d5664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2393, d5664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19618 p hg
    simpa only [d2393, d5664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19702 (p : Pattern) (guard : d5540 p = 1) : d2394 p ≤ (0 : Int) + d5667 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2394, d5667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19701 p hg
    simpa only [d2394, d5667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2394, d5667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19621 p hg
    simpa only [d2394, d5667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19703 (p : Pattern) (guard : d5540 p = 1) : d2395 p ≤ (0 : Int) + d5682 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2395, d5682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19702 p hg
    simpa only [d2395, d5682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2395, d5682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19640 p hg
    simpa only [d2395, d5682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19704 (p : Pattern) (guard : d5540 p = 1) : d2377 p ≤ (0 : Int) + d5687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2377, d5687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19608 p hg
    simpa only [d2377, d5687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2377, d5687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19650 p hg
    simpa only [d2377, d5687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19705 (p : Pattern) (guard : d5540 p = 1) : d2378 p ≤ (0 : Int) + d5689 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2378, d5689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19704 p hg
    simpa only [d2378, d5689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2378, d5689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19652 p hg
    simpa only [d2378, d5689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19706 (p : Pattern) (guard : d5540 p = 1) : d2379 p ≤ (0 : Int) + d5692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2379, d5692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19705 p hg
    simpa only [d2379, d5692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2379, d5692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19655 p hg
    simpa only [d2379, d5692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19707 (p : Pattern) (guard : d5540 p = 1) : d2396 p ≤ (0 : Int) + d5700 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2396, d5700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19706 p hg
    simpa only [d2396, d5700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2396, d5700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19663 p hg
    simpa only [d2396, d5700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19708 (p : Pattern) (guard : d5540 p = 1) : d2397 p ≤ (0 : Int) + d5701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2397, d5701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19703 p hg
    simpa only [d2397, d5701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2397, d5701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19707 p hg
    simpa only [d2397, d5701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19709 (p : Pattern) (guard : d5540 p = 1) : d2398 p ≤ (0 : Int) + d5728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2398, d5728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19708 p hg
    simpa only [d2398, d5728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2398, d5728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19692 p hg
    simpa only [d2398, d5728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19710 (p : Pattern) (guard : d5540 p = 1) : d2399 p ≤ (0 : Int) + d5735 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2399, d5735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19692 p hg
    simpa only [d2399, d5735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2399, d5735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2399, d5735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19711 (p : Pattern) (guard : d5540 p = 1) : d2400 p ≤ (0 : Int) + d5736 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2400, d5736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19709 p hg
    simpa only [d2400, d5736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2400, d5736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19710 p hg
    simpa only [d2400, d5736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19712 (p : Pattern) (guard : d5540 p = 1) : d2401 p ≤ (0 : Int) + d5737 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2401, d5737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19699 p hg
    simpa only [d2401, d5737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2401, d5737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19711 p hg
    simpa only [d2401, d5737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19713 (p : Pattern) (guard : d5540 p = 1) : d2402 p ≤ (0 : Int) + d5738 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2402, d5738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19568 p hg
    simpa only [d2402, d5738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2402, d5738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19712 p hg
    simpa only [d2402, d5738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19714 (p : Pattern) (guard : d5540 p = 1) : d2403 p ≤ (0 : Int) + d5739 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2403, d5739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19592 p hg
    simpa only [d2403, d5739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2403, d5739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19713 p hg
    simpa only [d2403, d5739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19715 (p : Pattern) (guard : d5540 p = 1) : d2404 p ≤ (0 : Int) + d5740 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2404, d5740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d2404, d5740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2404, d5740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19453 p hg
    simpa only [d2404, d5740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19716 (p : Pattern) (guard : d5540 p = 1) : d2405 p ≤ (0 : Int) + d5741 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2405, d5741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d2405, d5741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2405, d5741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19715 p hg
    simpa only [d2405, d5741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19717 (p : Pattern) (guard : d5540 p = 1) : d2406 p ≤ (0 : Int) + d5742 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2406, d5742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d2406, d5742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2406, d5742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19459 p hg
    simpa only [d2406, d5742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19718 (p : Pattern) (guard : d5540 p = 1) : d2407 p ≤ (0 : Int) + d5743 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2407, d5743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19522 p hg
    simpa only [d2407, d5743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2407, d5743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2407, d5743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19719 (p : Pattern) (guard : d5540 p = 1) : d2408 p ≤ (0 : Int) + d5744 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2408, d5744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19717 p hg
    simpa only [d2408, d5744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2408, d5744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19718 p hg
    simpa only [d2408, d5744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19720 (p : Pattern) (guard : d5540 p = 1) : d2409 p ≤ (0 : Int) + d5745 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2409, d5745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19716 p hg
    simpa only [d2409, d5745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2409, d5745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19719 p hg
    simpa only [d2409, d5745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19721 (p : Pattern) (guard : d5540 p = 1) : d2410 p ≤ (0 : Int) + d5746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2410, d5746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19497 p hg
    simpa only [d2410, d5746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2410, d5746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19718 p hg
    simpa only [d2410, d5746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19722 (p : Pattern) (guard : d5540 p = 1) : d2411 p ≤ (0 : Int) + d5747 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2411, d5747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19721 p hg
    simpa only [d2411, d5747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2411, d5747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19504 p hg
    simpa only [d2411, d5747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19723 (p : Pattern) (guard : d5540 p = 1) : d2412 p ≤ (0 : Int) + d5748 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2412, d5748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19720 p hg
    simpa only [d2412, d5748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2412, d5748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19722 p hg
    simpa only [d2412, d5748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19724 (p : Pattern) (guard : d5540 p = 1) : d2413 p ≤ (0 : Int) + d5749 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2413, d5749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19543 p hg
    simpa only [d2413, d5749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2413, d5749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19723 p hg
    simpa only [d2413, d5749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19725 (p : Pattern) (guard : d5540 p = 1) : d2414 p ≤ (0 : Int) + d5750 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2414, d5750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19715 p hg
    simpa only [d2414, d5750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2414, d5750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d2414, d5750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19726 (p : Pattern) (guard : d5540 p = 1) : d2415 p ≤ (0 : Int) + d5751 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2415, d5751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19718 p hg
    simpa only [d2415, d5751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2415, d5751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19503 p hg
    simpa only [d2415, d5751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19727 (p : Pattern) (guard : d5540 p = 1) : d2416 p ≤ (0 : Int) + d5752 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2416, d5752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19725 p hg
    simpa only [d2416, d5752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2416, d5752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19726 p hg
    simpa only [d2416, d5752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19728 (p : Pattern) (guard : d5540 p = 1) : d2417 p ≤ (0 : Int) + d5753 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2417, d5753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19718 p hg
    simpa only [d2417, d5753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2417, d5753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2417, d5753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19729 (p : Pattern) (guard : d5540 p = 1) : d2418 p ≤ (0 : Int) + d5754 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2418, d5754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19728 p hg
    simpa only [d2418, d5754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2418, d5754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2418, d5754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19730 (p : Pattern) (guard : d5540 p = 1) : d2419 p ≤ (0 : Int) + d5755 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2419, d5755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19727 p hg
    simpa only [d2419, d5755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2419, d5755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19729 p hg
    simpa only [d2419, d5755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19731 (p : Pattern) (guard : d5540 p = 1) : d2420 p ≤ (0 : Int) + d5756 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2420, d5756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19533 p hg
    simpa only [d2420, d5756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2420, d5756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19730 p hg
    simpa only [d2420, d5756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19732 (p : Pattern) (guard : d5540 p = 1) : d2421 p ≤ (0 : Int) + d5757 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2421, d5757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19724 p hg
    simpa only [d2421, d5757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2421, d5757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19731 p hg
    simpa only [d2421, d5757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19733 (p : Pattern) (guard : d5540 p = 1) : d2422 p ≤ (0 : Int) + d5758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2422, d5758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19510 p hg
    simpa only [d2422, d5758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2422, d5758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19524 p hg
    simpa only [d2422, d5758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19734 (p : Pattern) (guard : d5540 p = 1) : d2423 p ≤ (0 : Int) + d5759 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2423, d5759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19733 p hg
    simpa only [d2423, d5759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2423, d5759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19525 p hg
    simpa only [d2423, d5759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19735 (p : Pattern) (guard : d5501 p = 1) : d191 p ≤ (0 : Int) + d191 p := by
  omega
theorem compare19736 (p : Pattern) (guard : d5540 p = 1) : d2424 p ≤ (0 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19735 p hg
    simpa only [d5540, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15557 p hg
    simpa only [d5540, d2424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19737 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19738 (p : Pattern) (guard : d5540 p = 1) : d2424 p ≤ (0 : Int) + d5760 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2424, d5760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19735 p hg
    simpa only [d5540, d2424, d5760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2424, d5760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5540, d2424, d5760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19739 (p : Pattern) (guard : d5540 p = 1) : d2424 p ≤ (0 : Int) + d5761 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19736 p hg
    simpa only [d5761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19738 p hg
    simpa only [d5761, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
