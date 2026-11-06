/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11480 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d1730 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11481 (p : Pattern) (guard : d4967 p = 1) : d42 p ≤ (0 : Int) + d1731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d42, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d42, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d42, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d4967, d42, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11482 (p : Pattern) (guard : d4967 p = 1) : d43 p ≤ (0 : Int) + d1732 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d43, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d43, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d43, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d43, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11483 (p : Pattern) (guard : d4967 p = 1) : d44 p ≤ (0 : Int) + d1733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d44, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11481 p hg
    simpa only [d44, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d44, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d44, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11484 (p : Pattern) (guard : d4967 p = 1) : d45 p ≤ (0 : Int) + d1734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d45, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11479 p hg
    simpa only [d45, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d45, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11483 p hg
    simpa only [d45, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11485 (p : Pattern) (guard : d4967 p = 1) : d46 p ≤ (0 : Int) + d1735 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d46, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d46, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d46, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d46, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11486 (p : Pattern) (guard : d4967 p = 1) : d47 p ≤ (0 : Int) + d1736 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d47, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11485 p hg
    simpa only [d47, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d47, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d47, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11487 (p : Pattern) (guard : d4967 p = 1) : d48 p ≤ (0 : Int) + d527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d48, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d4967, d48, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d48, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d48, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11488 (p : Pattern) (guard : d4967 p = 1) : d49 p ≤ (0 : Int) + d528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d49, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d49, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d49, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d49, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11489 (p : Pattern) (guard : d4967 p = 1) : d50 p ≤ (0 : Int) + d1737 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d50, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11486 p hg
    simpa only [d50, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d50, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11488 p hg
    simpa only [d50, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11490 (p : Pattern) (guard : d4967 p = 1) : d51 p ≤ (0 : Int) + d1738 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d51, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11484 p hg
    simpa only [d51, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d51, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11489 p hg
    simpa only [d51, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11491 (p : Pattern) (guard : d4967 p = 1) : d52 p ≤ (0 : Int) + d1739 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d52, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11474 p hg
    simpa only [d52, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d52, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d52, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11492 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d335 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11493 (p : Pattern) (guard : d4474 p = 1) : d14 p ≤ (0 : Int) + d1740 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11492 p hg
    simpa only [d4474, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11494 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1741 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11493 p hg
    simpa only [d4967, d16, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d4967, d16, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11495 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11496 (p : Pattern) (guard : d4474 p = 1) : d31 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d4474, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11497 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d1746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11498 (p : Pattern) (guard : d4967 p = 1) : d53 p ≤ (0 : Int) + d1747 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d53, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d53, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d53, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11497 p hg
    simpa only [d4967, d53, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11499 (p : Pattern) (guard : d4967 p = 1) : d54 p ≤ (0 : Int) + d1748 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d54, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11494 p hg
    simpa only [d54, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d54, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d54, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11500 (p : Pattern) (guard : d4967 p = 1) : d55 p ≤ (0 : Int) + d1749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d55, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d55, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d55, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11470 p hg
    simpa only [d55, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11501 (p : Pattern) (guard : d4967 p = 1) : d56 p ≤ (0 : Int) + d1750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d56, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11499 p hg
    simpa only [d56, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d56, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11500 p hg
    simpa only [d56, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11502 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11503 (p : Pattern) (guard : d4474 p = 1) : d58 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d4474, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11504 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d1753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11505 (p : Pattern) (guard : d4967 p = 1) : d60 p ≤ (0 : Int) + d1754 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d60, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11503 p hg
    simpa only [d4967, d60, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d60, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11504 p hg
    simpa only [d4967, d60, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11506 (p : Pattern) (guard : d4967 p = 1) : d61 p ≤ (0 : Int) + d1755 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d61, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11464 p hg
    simpa only [d61, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d61, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d61, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11507 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11508 (p : Pattern) (guard : d4474 p = 1) : d40 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d4474, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11509 (p : Pattern) (guard : d4967 p = 1) : d62 p ≤ (0 : Int) + d1756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d62, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d4967, d62, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d62, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11480 p hg
    simpa only [d4967, d62, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11510 (p : Pattern) (guard : d4967 p = 1) : d63 p ≤ (0 : Int) + d1757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d63, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d63, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d63, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d63, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11511 (p : Pattern) (guard : d4967 p = 1) : d64 p ≤ (0 : Int) + d1758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d64, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11506 p hg
    simpa only [d64, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d64, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d64, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11512 (p : Pattern) (guard : d4967 p = 1) : d65 p ≤ (0 : Int) + d1759 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d65, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11501 p hg
    simpa only [d65, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d65, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11511 p hg
    simpa only [d65, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11513 (p : Pattern) (guard : d4967 p = 1) : d66 p ≤ (0 : Int) + d1760 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d66, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d66, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d66, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d66, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11514 (p : Pattern) (guard : d4967 p = 1) : d67 p ≤ (0 : Int) + d1761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d67, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11478 p hg
    simpa only [d67, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d67, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11513 p hg
    simpa only [d67, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11515 (p : Pattern) (guard : d4967 p = 1) : d68 p ≤ (0 : Int) + d1762 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d68, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d68, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d68, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11487 p hg
    simpa only [d68, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11516 (p : Pattern) (guard : d4967 p = 1) : d69 p ≤ (0 : Int) + d1763 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d69, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11514 p hg
    simpa only [d69, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d69, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11515 p hg
    simpa only [d69, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11517 (p : Pattern) (guard : d4967 p = 1) : d70 p ≤ (0 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d70, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11503 p hg
    simpa only [d4967, d70, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d70, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d70, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11518 (p : Pattern) (guard : d4967 p = 1) : d71 p ≤ (0 : Int) + d1764 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d71, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11482 p hg
    simpa only [d71, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d71, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11517 p hg
    simpa only [d71, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11519 (p : Pattern) (guard : d4967 p = 1) : d72 p ≤ (0 : Int) + d538 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d72, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11508 p hg
    simpa only [d4967, d72, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d72, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4967, d72, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11520 (p : Pattern) (guard : d4967 p = 1) : d73 p ≤ (0 : Int) + d539 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d73, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11519 p hg
    simpa only [d73, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d73, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d73, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11521 (p : Pattern) (guard : d4967 p = 1) : d74 p ≤ (0 : Int) + d1765 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d74, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11518 p hg
    simpa only [d74, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d74, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11520 p hg
    simpa only [d74, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11522 (p : Pattern) (guard : d4967 p = 1) : d75 p ≤ (0 : Int) + d1766 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d75, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11516 p hg
    simpa only [d75, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d75, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11521 p hg
    simpa only [d75, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11523 (p : Pattern) (guard : d4967 p = 1) : d76 p ≤ (0 : Int) + d1767 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d76, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11512 p hg
    simpa only [d76, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d76, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d76, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11524 (p : Pattern) (guard : d4967 p = 1) : d77 p ≤ (0 : Int) + d1768 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d77, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11491 p hg
    simpa only [d77, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d77, d1768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11523 p hg
    simpa only [d77, d1768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11525 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d1773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11526 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11525 p hg
    simpa only [d4967, d16, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11527 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d1782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11528 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1783 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11527 p hg
    simpa only [d4967, d16, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11529 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11526 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11528 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11530 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d1789 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11531 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1790 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11459 p hg
    simpa only [d4967, d16, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11530 p hg
    simpa only [d4967, d16, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11532 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d1798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11533 (p : Pattern) (guard : d4967 p = 1) : d20 p ≤ (0 : Int) + d1799 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d20, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11462 p hg
    simpa only [d4967, d20, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d20, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11532 p hg
    simpa only [d4967, d20, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11534 (p : Pattern) (guard : d4967 p = 1) : d21 p ≤ (0 : Int) + d1800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d21, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11531 p hg
    simpa only [d21, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d21, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d21, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11535 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d1801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11529 p hg
    simpa only [d22, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11534 p hg
    simpa only [d22, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11536 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d1804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11537 (p : Pattern) (guard : d4967 p = 1) : d26 p ≤ (0 : Int) + d1805 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d26, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11468 p hg
    simpa only [d4967, d26, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d26, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11536 p hg
    simpa only [d4967, d26, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11538 (p : Pattern) (guard : d4967 p = 1) : d27 p ≤ (0 : Int) + d1806 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d27, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d27, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d27, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d27, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11539 (p : Pattern) (guard : d4967 p = 1) : d28 p ≤ (0 : Int) + d1807 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d28, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11534 p hg
    simpa only [d28, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d28, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11538 p hg
    simpa only [d28, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11540 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d1808 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11535 p hg
    simpa only [d29, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11539 p hg
    simpa only [d29, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11541 (p : Pattern) (guard : d4967 p = 1) : d53 p ≤ (0 : Int) + d1809 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d53, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11496 p hg
    simpa only [d4967, d53, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d53, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11475 p hg
    simpa only [d4967, d53, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11542 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11543 (p : Pattern) (guard : d4474 p = 1) : d35 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11544 (p : Pattern) (guard : d4967 p = 1) : d78 p ≤ (0 : Int) + d1810 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d78, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11543 p hg
    simpa only [d4967, d78, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d78, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11477 p hg
    simpa only [d4967, d78, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11545 (p : Pattern) (guard : d4967 p = 1) : d79 p ≤ (0 : Int) + d1811 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d79, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d79, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d79, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11544 p hg
    simpa only [d79, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11546 (p : Pattern) (guard : d4967 p = 1) : d80 p ≤ (0 : Int) + d1812 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d80, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11545 p hg
    simpa only [d80, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d80, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d80, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11547 (p : Pattern) (guard : d4967 p = 1) : d81 p ≤ (0 : Int) + d1813 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d81, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11546 p hg
    simpa only [d81, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d81, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d81, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11548 (p : Pattern) (guard : d4967 p = 1) : d82 p ≤ (0 : Int) + d1814 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d82, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11540 p hg
    simpa only [d82, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d82, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11547 p hg
    simpa only [d82, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11549 (p : Pattern) (guard : d4967 p = 1) : d54 p ≤ (0 : Int) + d1815 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d54, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11528 p hg
    simpa only [d54, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d54, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11541 p hg
    simpa only [d54, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11550 (p : Pattern) (guard : d4967 p = 1) : d55 p ≤ (0 : Int) + d1816 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d55, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d55, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d55, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d55, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11551 (p : Pattern) (guard : d4967 p = 1) : d56 p ≤ (0 : Int) + d1817 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d56, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11549 p hg
    simpa only [d56, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d56, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11550 p hg
    simpa only [d56, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11552 (p : Pattern) (guard : d4967 p = 1) : d61 p ≤ (0 : Int) + d1818 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d61, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11533 p hg
    simpa only [d61, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d61, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11505 p hg
    simpa only [d61, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11553 (p : Pattern) (guard : d4967 p = 1) : d64 p ≤ (0 : Int) + d1819 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d64, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11552 p hg
    simpa only [d64, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d64, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d64, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11554 (p : Pattern) (guard : d4967 p = 1) : d65 p ≤ (0 : Int) + d1820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d65, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11551 p hg
    simpa only [d65, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d65, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11553 p hg
    simpa only [d65, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11555 (p : Pattern) (guard : d4967 p = 1) : d83 p ≤ (0 : Int) + d1821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d83, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11544 p hg
    simpa only [d83, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d83, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d83, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11556 (p : Pattern) (guard : d4967 p = 1) : d84 p ≤ (0 : Int) + d1822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d84, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11555 p hg
    simpa only [d84, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d84, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d84, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11557 (p : Pattern) (guard : d4967 p = 1) : d85 p ≤ (0 : Int) + d1823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d85, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11556 p hg
    simpa only [d85, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d85, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d85, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11558 (p : Pattern) (guard : d4967 p = 1) : d86 p ≤ (0 : Int) + d1824 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d86, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11554 p hg
    simpa only [d86, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d86, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11557 p hg
    simpa only [d86, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11559 (p : Pattern) (guard : d4967 p = 1) : d87 p ≤ (0 : Int) + d1825 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d87, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11548 p hg
    simpa only [d87, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d87, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11558 p hg
    simpa only [d87, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11560 (p : Pattern) (guard : d4967 p = 1) : d88 p ≤ (0 : Int) + d1826 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d88, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11524 p hg
    simpa only [d88, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d88, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d88, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11561 (p : Pattern) (guard : d4967 p = 1) : d89 p ≤ (0 : Int) + d1827 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d89, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11537 p hg
    simpa only [d89, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d89, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11509 p hg
    simpa only [d89, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11562 (p : Pattern) (guard : d4967 p = 1) : d90 p ≤ (0 : Int) + d1828 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d90, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11561 p hg
    simpa only [d90, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d90, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d90, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11563 (p : Pattern) (guard : d4967 p = 1) : d91 p ≤ (0 : Int) + d1829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d91, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11510 p hg
    simpa only [d91, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d91, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d91, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11564 (p : Pattern) (guard : d4967 p = 1) : d92 p ≤ (0 : Int) + d1830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d92, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11562 p hg
    simpa only [d92, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d92, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11563 p hg
    simpa only [d92, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11565 (p : Pattern) (guard : d4967 p = 1) : d93 p ≤ (0 : Int) + d1831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d93, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11563 p hg
    simpa only [d93, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d93, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d93, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11566 (p : Pattern) (guard : d4967 p = 1) : d94 p ≤ (0 : Int) + d1832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d94, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11564 p hg
    simpa only [d94, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d94, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11565 p hg
    simpa only [d94, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11567 (p : Pattern) (guard : d4967 p = 1) : d95 p ≤ (0 : Int) + d1833 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d95, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11565 p hg
    simpa only [d95, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d95, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d95, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11568 (p : Pattern) (guard : d4967 p = 1) : d96 p ≤ (0 : Int) + d1834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d96, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11566 p hg
    simpa only [d96, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d96, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11567 p hg
    simpa only [d96, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11569 (p : Pattern) (guard : d4967 p = 1) : d97 p ≤ (0 : Int) + d1835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d97, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d97, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d97, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11568 p hg
    simpa only [d97, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11570 (p : Pattern) (guard : d4967 p = 1) : d98 p ≤ (0 : Int) + d1836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d98, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11560 p hg
    simpa only [d98, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d98, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11569 p hg
    simpa only [d98, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11571 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1837 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11456 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11572 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d1838 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11571 p hg
    simpa only [d22, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d22, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11573 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d1839 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11572 p hg
    simpa only [d29, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d29, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11574 (p : Pattern) (guard : d4967 p = 1) : d52 p ≤ (0 : Int) + d1840 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d52, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11573 p hg
    simpa only [d52, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d52, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d52, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11575 (p : Pattern) (guard : d4967 p = 1) : d54 p ≤ (0 : Int) + d1841 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d54, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d54, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d54, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d54, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11576 (p : Pattern) (guard : d4967 p = 1) : d56 p ≤ (0 : Int) + d1842 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d56, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11575 p hg
    simpa only [d56, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d56, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11500 p hg
    simpa only [d56, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11577 (p : Pattern) (guard : d4967 p = 1) : d65 p ≤ (0 : Int) + d1843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d65, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11576 p hg
    simpa only [d65, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d65, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11511 p hg
    simpa only [d65, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11578 (p : Pattern) (guard : d4967 p = 1) : d76 p ≤ (0 : Int) + d1844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d76, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11577 p hg
    simpa only [d76, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d76, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d76, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11579 (p : Pattern) (guard : d4967 p = 1) : d77 p ≤ (0 : Int) + d1845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d77, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11574 p hg
    simpa only [d77, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d77, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11578 p hg
    simpa only [d77, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11580 (p : Pattern) (guard : d4967 p = 1) : d88 p ≤ (0 : Int) + d1846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d88, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11579 p hg
    simpa only [d88, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d88, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d88, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11581 (p : Pattern) (guard : d4967 p = 1) : d99 p ≤ (0 : Int) + d1847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d99, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d99, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d99, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d99, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11582 (p : Pattern) (guard : d4967 p = 1) : d100 p ≤ (0 : Int) + d1848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d100, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11580 p hg
    simpa only [d100, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d100, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11581 p hg
    simpa only [d100, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11583 (p : Pattern) (guard : d4967 p = 1) : d101 p ≤ (0 : Int) + d1849 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d101, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11570 p hg
    simpa only [d101, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d101, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11582 p hg
    simpa only [d101, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11584 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11585 (p : Pattern) (guard : d4474 p = 1) : d14 p ≤ (0 : Int) + d1850 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11584 p hg
    simpa only [d4474, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11586 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1851 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d16, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11585 p hg
    simpa only [d4967, d16, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d16, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11452 p hg
    simpa only [d4967, d16, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11587 (p : Pattern) (guard : d4967 p = 1) : d16 p ≤ (0 : Int) + d1852 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11586 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11588 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d1853 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11587 p hg
    simpa only [d22, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d22, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11589 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d1854 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11588 p hg
    simpa only [d29, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d29, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11590 (p : Pattern) (guard : d4967 p = 1) : d52 p ≤ (0 : Int) + d1855 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d52, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11589 p hg
    simpa only [d52, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d52, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d52, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11591 (p : Pattern) (guard : d4967 p = 1) : d54 p ≤ (0 : Int) + d1856 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d54, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11456 p hg
    simpa only [d54, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d54, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11498 p hg
    simpa only [d54, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11592 (p : Pattern) (guard : d4967 p = 1) : d56 p ≤ (0 : Int) + d1857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d56, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11591 p hg
    simpa only [d56, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d56, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11500 p hg
    simpa only [d56, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11593 (p : Pattern) (guard : d4967 p = 1) : d65 p ≤ (0 : Int) + d1858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d65, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11592 p hg
    simpa only [d65, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d65, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11511 p hg
    simpa only [d65, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11594 (p : Pattern) (guard : d4967 p = 1) : d76 p ≤ (0 : Int) + d1859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d76, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11593 p hg
    simpa only [d76, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d76, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11522 p hg
    simpa only [d76, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11595 (p : Pattern) (guard : d4967 p = 1) : d77 p ≤ (0 : Int) + d1860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d77, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11590 p hg
    simpa only [d77, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d77, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11594 p hg
    simpa only [d77, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11596 (p : Pattern) (guard : d4967 p = 1) : d88 p ≤ (0 : Int) + d1861 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d88, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11595 p hg
    simpa only [d88, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d88, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d88, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11597 (p : Pattern) (guard : d4967 p = 1) : d98 p ≤ (0 : Int) + d1862 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d98, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11596 p hg
    simpa only [d98, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d98, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11569 p hg
    simpa only [d98, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11598 (p : Pattern) (guard : d4967 p = 1) : d22 p ≤ (0 : Int) + d1863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d22, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11460 p hg
    simpa only [d22, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d22, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11465 p hg
    simpa only [d22, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11599 (p : Pattern) (guard : d4967 p = 1) : d29 p ≤ (0 : Int) + d1864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d29, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11598 p hg
    simpa only [d29, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d29, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11473 p hg
    simpa only [d29, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11600 (p : Pattern) (guard : d4967 p = 1) : d52 p ≤ (0 : Int) + d1865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d52, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11599 p hg
    simpa only [d52, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d52, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11490 p hg
    simpa only [d52, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11601 (p : Pattern) (guard : d4967 p = 1) : d77 p ≤ (0 : Int) + d1866 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d77, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11600 p hg
    simpa only [d77, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d77, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11578 p hg
    simpa only [d77, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11602 (p : Pattern) (guard : d4967 p = 1) : d88 p ≤ (0 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d88, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11601 p hg
    simpa only [d88, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d88, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11559 p hg
    simpa only [d88, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11603 (p : Pattern) (guard : d4967 p = 1) : d100 p ≤ (0 : Int) + d1868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d100, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11602 p hg
    simpa only [d100, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d100, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11581 p hg
    simpa only [d100, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11604 (p : Pattern) (guard : d4967 p = 1) : d101 p ≤ (0 : Int) + d1869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d101, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11597 p hg
    simpa only [d101, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d101, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11603 p hg
    simpa only [d101, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11605 (p : Pattern) (guard : d4967 p = 1) : d101 p ≤ (0 : Int) + d1870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11583 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11604 p hg
    simpa only [d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11606 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d358 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11607 (p : Pattern) (guard : d4474 p = 1) : d103 p ≤ (0 : Int) + d1871 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11606 p hg
    simpa only [d4474, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11608 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d1876 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11609 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1877 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11607 p hg
    simpa only [d4967, d105, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d4967, d105, d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11610 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11611 (p : Pattern) (guard : d4474 p = 1) : d103 p ≤ (0 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11612 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1878 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d105, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11611 p hg
    simpa only [d4967, d105, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d105, d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11608 p hg
    simpa only [d4967, d105, d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11613 (p : Pattern) (guard : d4967 p = 1) : d105 p ≤ (0 : Int) + d1879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11609 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11614 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11615 (p : Pattern) (guard : d4474 p = 1) : d107 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11616 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d1884 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11617 (p : Pattern) (guard : d4967 p = 1) : d109 p ≤ (0 : Int) + d1885 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d109, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11615 p hg
    simpa only [d4967, d109, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d109, d1885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11616 p hg
    simpa only [d4967, d109, d1885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11618 (p : Pattern) (guard : d4967 p = 1) : d110 p ≤ (0 : Int) + d1886 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d110, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11612 p hg
    simpa only [d110, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d110, d1886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11617 p hg
    simpa only [d110, d1886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11619 (p : Pattern) (guard : d4967 p = 1) : d111 p ≤ (0 : Int) + d1887 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d111, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11613 p hg
    simpa only [d111, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d111, d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11618 p hg
    simpa only [d111, d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
