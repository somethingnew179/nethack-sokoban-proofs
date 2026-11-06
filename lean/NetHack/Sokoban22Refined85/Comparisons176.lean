/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons175
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare24640 (p : Pattern) (guard : d4473 p = 1) : d3080 p ≤ (2 : Int) + d2012 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24633 p hg
    simpa only [d4473, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24639 p hg
    simpa only [d4473, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24641 (p : Pattern) (guard : d0 p = 1) : d2013 p ≤ (2 : Int) + d2012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24642 (p : Pattern) (guard : d4985 p = 1) : d3081 p ≤ (2 : Int) + d2012 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24640 p hg
    simpa only [d4985, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24641 p hg
    simpa only [d4985, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24643 (p : Pattern) (guard : d4985 p = 1) : d3082 p ≤ (2 : Int) + d5952 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3082, d5952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24413 p hg
    simpa only [d3082, d5952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3082, d5952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24642 p hg
    simpa only [d3082, d5952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24644 (p : Pattern) (guard : d4985 p = 1) : d3083 p ≤ (2 : Int) + d5953 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3083, d5953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24413 p hg
    simpa only [d3083, d5953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3083, d5953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24643 p hg
    simpa only [d3083, d5953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24645 (p : Pattern) (guard : d4985 p = 1) : d3084 p ≤ (2 : Int) + d5954 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3084, d5954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24643 p hg
    simpa only [d3084, d5954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3084, d5954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24441 p hg
    simpa only [d3084, d5954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24646 (p : Pattern) (guard : d4985 p = 1) : d3085 p ≤ (2 : Int) + d5955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3085, d5955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24644 p hg
    simpa only [d3085, d5955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3085, d5955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24645 p hg
    simpa only [d3085, d5955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24647 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24648 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d6 p := by
  change (2 : Int) ≤ (2 : Int) + 6
  decide
theorem compare24649 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24650 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24649 p hg
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24651 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d1710, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d1710, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24652 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (2 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24651 p hg
    simpa only [d1711, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d1711, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24653 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d1720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24650 p hg
    simpa only [d1712, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24652 p hg
    simpa only [d1712, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24654 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d10 p := by
  change (6 : Int) ≤ (2 : Int) + 10
  decide
theorem compare24655 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d1721 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24648 p hg
    simpa only [d1713, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24654 p hg
    simpa only [d1713, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24656 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24654 p hg
    simpa only [d34, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24657 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d1722 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24655 p hg
    simpa only [d1714, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24656 p hg
    simpa only [d1714, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24658 (p : Pattern) (guard : d1 p = 1) : d1715 p ≤ (2 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1715, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24649 p hg
    simpa only [d1715, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1715, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1715, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24659 (p : Pattern) (guard : d1 p = 1) : d1716 p ≤ (2 : Int) + d1723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1716, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24657 p hg
    simpa only [d1716, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1716, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24658 p hg
    simpa only [d1716, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24660 (p : Pattern) (guard : d1 p = 1) : d1717 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1717, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24653 p hg
    simpa only [d1717, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1717, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24659 p hg
    simpa only [d1717, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24661 (p : Pattern) (guard : d4473 p = 1) : d2935 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24647 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24660 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24662 (p : Pattern) (guard : d4985 p = 1) : d3086 p ≤ (2 : Int) + d1724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24661 p hg
    simpa only [d4985, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24330 p hg
    simpa only [d4985, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24663 (p : Pattern) (guard : d4985 p = 1) : d3087 p ≤ (2 : Int) + d5861 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3087, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24447 p hg
    simpa only [d3087, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3087, d5861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24662 p hg
    simpa only [d3087, d5861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24664 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d1729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24665 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d11 p := by
  change (2 : Int) ≤ (2 : Int) + 11
  decide
theorem compare24666 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24665 p hg
    simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24667 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24665 p hg
    simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24666 p hg
    simpa only [d31, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24668 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24665 p hg
    simpa only [d1710, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d1710, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24669 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24668 p hg
    simpa only [d1711, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d1711, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24670 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d1728 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24667 p hg
    simpa only [d1712, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24669 p hg
    simpa only [d1712, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24671 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24665 p hg
    simpa only [d1713, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1713, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24672 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24671 p hg
    simpa only [d1714, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1714, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24673 (p : Pattern) (guard : d1 p = 1) : d1715 p ≤ (2 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1715, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24666 p hg
    simpa only [d1715, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1715, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d1715, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24674 (p : Pattern) (guard : d1 p = 1) : d1716 p ≤ (2 : Int) + d327 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24672 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24673 p hg
    simpa only [d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24675 (p : Pattern) (guard : d1 p = 1) : d1717 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1717, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24670 p hg
    simpa only [d1717, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1717, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24674 p hg
    simpa only [d1717, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24676 (p : Pattern) (guard : d4473 p = 1) : d2935 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24664 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24675 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24677 (p : Pattern) (guard : d4985 p = 1) : d3088 p ≤ (2 : Int) + d1729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24676 p hg
    simpa only [d4985, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24344 p hg
    simpa only [d4985, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24678 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24679 (p : Pattern) (guard : d4473 p = 1) : d2962 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24678 p hg
    simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16141 p hg
    simpa only [d4473, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24680 (p : Pattern) (guard : d4985 p = 1) : d3089 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24679 p hg
    simpa only [d4985, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4985, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24681 (p : Pattern) (guard : d4985 p = 1) : d3090 p ≤ (2 : Int) + d5862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3090, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24677 p hg
    simpa only [d3090, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3090, d5862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d3090, d5862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24682 (p : Pattern) (guard : d4985 p = 1) : d3091 p ≤ (2 : Int) + d5863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3091, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24663 p hg
    simpa only [d3091, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3091, d5863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24681 p hg
    simpa only [d3091, d5863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24683 (p : Pattern) (guard : d4985 p = 1) : d3092 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24388 p hg
    simpa only [d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24684 (p : Pattern) (guard : d4985 p = 1) : d3093 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24683 p hg
    simpa only [d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24399 p hg
    simpa only [d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24685 (p : Pattern) (guard : d4985 p = 1) : d3094 p ≤ (2 : Int) + d5864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3094, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24682 p hg
    simpa only [d3094, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3094, d5864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24684 p hg
    simpa only [d3094, d5864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24686 (p : Pattern) (guard : d4985 p = 1) : d3095 p ≤ (2 : Int) + d5956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3095, d5956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24646 p hg
    simpa only [d3095, d5956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3095, d5956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24685 p hg
    simpa only [d3095, d5956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24687 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d2030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24688 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (2 : Int) + d1713 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d1710, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d1710, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24689 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24688 p hg
    simpa only [d1711, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d1711, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24690 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d2029 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1712, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24689 p hg
    simpa only [d1712, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24691 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d1714 p := by
  omega
theorem compare24692 (p : Pattern) (guard : d1 p = 1) : d3096 p ≤ (2 : Int) + d1714 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24691 p hg
    simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24689 p hg
    simpa only [d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24693 (p : Pattern) (guard : d1 p = 1) : d3097 p ≤ (2 : Int) + d2030 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3097, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24690 p hg
    simpa only [d3097, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3097, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24692 p hg
    simpa only [d3097, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24694 (p : Pattern) (guard : d4473 p = 1) : d3098 p ≤ (2 : Int) + d2030 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24687 p hg
    simpa only [d4473, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24693 p hg
    simpa only [d4473, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24695 (p : Pattern) (guard : d0 p = 1) : d2031 p ≤ (2 : Int) + d2030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24696 (p : Pattern) (guard : d4985 p = 1) : d3099 p ≤ (2 : Int) + d2030 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24694 p hg
    simpa only [d4985, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24695 p hg
    simpa only [d4985, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24697 (p : Pattern) (guard : d4985 p = 1) : d3100 p ≤ (2 : Int) + d5957 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3100, d5957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24413 p hg
    simpa only [d3100, d5957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3100, d5957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24696 p hg
    simpa only [d3100, d5957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24698 (p : Pattern) (guard : d4985 p = 1) : d3101 p ≤ (2 : Int) + d5958 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3101, d5958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24642 p hg
    simpa only [d3101, d5958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3101, d5958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24440 p hg
    simpa only [d3101, d5958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24699 (p : Pattern) (guard : d4985 p = 1) : d3102 p ≤ (2 : Int) + d5959 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3102, d5959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24697 p hg
    simpa only [d3102, d5959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3102, d5959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24698 p hg
    simpa only [d3102, d5959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24700 (p : Pattern) (guard : d4985 p = 1) : d3103 p ≤ (2 : Int) + d5960 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3103, d5960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24642 p hg
    simpa only [d3103, d5960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3103, d5960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24377 p hg
    simpa only [d3103, d5960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24701 (p : Pattern) (guard : d4985 p = 1) : d3104 p ≤ (2 : Int) + d5961 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3104, d5961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24700 p hg
    simpa only [d3104, d5961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3104, d5961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24383 p hg
    simpa only [d3104, d5961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24702 (p : Pattern) (guard : d4985 p = 1) : d3105 p ≤ (2 : Int) + d5962 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3105, d5962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24699 p hg
    simpa only [d3105, d5962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3105, d5962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24701 p hg
    simpa only [d3105, d5962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24703 (p : Pattern) (guard : d4985 p = 1) : d3106 p ≤ (2 : Int) + d5872 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3106, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24662 p hg
    simpa only [d3106, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3106, d5872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24348 p hg
    simpa only [d3106, d5872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24704 (p : Pattern) (guard : d4985 p = 1) : d3107 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24398 p hg
    simpa only [d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24705 (p : Pattern) (guard : d4985 p = 1) : d3108 p ≤ (2 : Int) + d5873 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3108, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24703 p hg
    simpa only [d3108, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3108, d5873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24704 p hg
    simpa only [d3108, d5873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24706 (p : Pattern) (guard : d4985 p = 1) : d3109 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24680 p hg
    simpa only [d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24707 (p : Pattern) (guard : d4985 p = 1) : d3110 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24706 p hg
    simpa only [d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24708 (p : Pattern) (guard : d4985 p = 1) : d3111 p ≤ (2 : Int) + d5874 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3111, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24705 p hg
    simpa only [d3111, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3111, d5874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24707 p hg
    simpa only [d3111, d5874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24709 (p : Pattern) (guard : d4985 p = 1) : d3112 p ≤ (2 : Int) + d5963 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3112, d5963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24702 p hg
    simpa only [d3112, d5963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3112, d5963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24708 p hg
    simpa only [d3112, d5963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24710 (p : Pattern) (guard : d4985 p = 1) : d3113 p ≤ (2 : Int) + d5964 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3113, d5964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24686 p hg
    simpa only [d3113, d5964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3113, d5964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24709 p hg
    simpa only [d3113, d5964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24711 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d2048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24712 (p : Pattern) (guard : d1 p = 1) : d1778 p ≤ (2 : Int) + d1775 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1778, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1778, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1778, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d1778, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24713 (p : Pattern) (guard : d1 p = 1) : d1779 p ≤ (2 : Int) + d1776 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1779, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24712 p hg
    simpa only [d1779, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1779, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d1779, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24714 (p : Pattern) (guard : d1 p = 1) : d1780 p ≤ (2 : Int) + d2047 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1780, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d1780, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1780, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24713 p hg
    simpa only [d1780, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24715 (p : Pattern) (guard : d1 p = 1) : d1781 p ≤ (2 : Int) + d2048 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1781, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24415 p hg
    simpa only [d1781, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1781, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24714 p hg
    simpa only [d1781, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24716 (p : Pattern) (guard : d4473 p = 1) : d3114 p ≤ (2 : Int) + d2048 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24711 p hg
    simpa only [d4473, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24715 p hg
    simpa only [d4473, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24717 (p : Pattern) (guard : d0 p = 1) : d2049 p ≤ (2 : Int) + d2048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24718 (p : Pattern) (guard : d4985 p = 1) : d3115 p ≤ (2 : Int) + d2048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24716 p hg
    simpa only [d4985, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24717 p hg
    simpa only [d4985, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24719 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d2054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24720 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d2051 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15669 p hg
    simpa only [d1785, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6088 p hg
    simpa only [d1785, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24721 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d2052 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24720 p hg
    simpa only [d1786, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16242 p hg
    simpa only [d1786, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24722 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d2053 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d1787, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24721 p hg
    simpa only [d1787, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24723 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d2054 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24415 p hg
    simpa only [d1788, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24722 p hg
    simpa only [d1788, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24724 (p : Pattern) (guard : d4473 p = 1) : d2906 p ≤ (2 : Int) + d2054 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24719 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24723 p hg
    simpa only [d4473, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24725 (p : Pattern) (guard : d0 p = 1) : d2055 p ≤ (2 : Int) + d2054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24726 (p : Pattern) (guard : d4985 p = 1) : d3116 p ≤ (2 : Int) + d2054 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24724 p hg
    simpa only [d4985, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24725 p hg
    simpa only [d4985, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24727 (p : Pattern) (guard : d4985 p = 1) : d3117 p ≤ (2 : Int) + d5965 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3117, d5965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24718 p hg
    simpa only [d3117, d5965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3117, d5965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24726 p hg
    simpa only [d3117, d5965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24728 (p : Pattern) (guard : d4985 p = 1) : d3118 p ≤ (2 : Int) + d5966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3118, d5966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24727 p hg
    simpa only [d3118, d5966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3118, d5966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24452 p hg
    simpa only [d3118, d5966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24729 (p : Pattern) (guard : d4985 p = 1) : d3119 p ≤ (2 : Int) + d5967 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3119, d5967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24728 p hg
    simpa only [d3119, d5967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3119, d5967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24453 p hg
    simpa only [d3119, d5967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24730 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (2 : Int) + d2061 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24731 (p : Pattern) (guard : d1 p = 1) : d2061 p ≤ (2 : Int) + d2061 p := by
  omega
theorem compare24732 (p : Pattern) (guard : d4473 p = 1) : d3120 p ≤ (2 : Int) + d2061 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24730 p hg
    simpa only [d4473, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24731 p hg
    simpa only [d4473, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24733 (p : Pattern) (guard : d0 p = 1) : d2062 p ≤ (2 : Int) + d2061 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24734 (p : Pattern) (guard : d4985 p = 1) : d3121 p ≤ (2 : Int) + d2061 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24732 p hg
    simpa only [d4985, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24733 p hg
    simpa only [d4985, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24735 (p : Pattern) (guard : d4985 p = 1) : d3122 p ≤ (2 : Int) + d5968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3122, d5968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d3122, d5968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3122, d5968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24734 p hg
    simpa only [d3122, d5968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24736 (p : Pattern) (guard : d4985 p = 1) : d3123 p ≤ (2 : Int) + d5969 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3123, d5969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24735 p hg
    simpa only [d3123, d5969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3123, d5969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3123, d5969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24737 (p : Pattern) (guard : d4985 p = 1) : d3124 p ≤ (2 : Int) + d5970 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3124, d5970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24736 p hg
    simpa only [d3124, d5970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3124, d5970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3124, d5970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24738 (p : Pattern) (guard : d4985 p = 1) : d3125 p ≤ (2 : Int) + d5971 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3125, d5971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24729 p hg
    simpa only [d3125, d5971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3125, d5971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24737 p hg
    simpa only [d3125, d5971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24739 (p : Pattern) (guard : d0 p = 1) : d31 p ≤ (2 : Int) + d2071 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24740 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d1712 p := by
  omega
theorem compare24741 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d2068 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d30, d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24742 (p : Pattern) (guard : d1 p = 1) : d1715 p ≤ (2 : Int) + d2069 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1715, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24741 p hg
    simpa only [d1715, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1715, d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6089 p hg
    simpa only [d1715, d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24743 (p : Pattern) (guard : d1 p = 1) : d1716 p ≤ (2 : Int) + d2070 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1716, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24691 p hg
    simpa only [d1716, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1716, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24742 p hg
    simpa only [d1716, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24744 (p : Pattern) (guard : d1 p = 1) : d1717 p ≤ (2 : Int) + d2071 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1717, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24740 p hg
    simpa only [d1717, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1717, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24743 p hg
    simpa only [d1717, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24745 (p : Pattern) (guard : d4473 p = 1) : d2935 p ≤ (2 : Int) + d2071 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24739 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24744 p hg
    simpa only [d4473, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24746 (p : Pattern) (guard : d0 p = 1) : d2072 p ≤ (2 : Int) + d2071 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare24747 (p : Pattern) (guard : d4985 p = 1) : d3126 p ≤ (2 : Int) + d2071 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24745 p hg
    simpa only [d4985, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24746 p hg
    simpa only [d4985, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24748 (p : Pattern) (guard : d4985 p = 1) : d3127 p ≤ (2 : Int) + d5972 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3127, d5972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24747 p hg
    simpa only [d3127, d5972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3127, d5972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24447 p hg
    simpa only [d3127, d5972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24749 (p : Pattern) (guard : d4985 p = 1) : d3128 p ≤ (2 : Int) + d5973 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3128, d5973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24433 p hg
    simpa only [d3128, d5973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3128, d5973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24382 p hg
    simpa only [d3128, d5973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24750 (p : Pattern) (guard : d4985 p = 1) : d3129 p ≤ (2 : Int) + d5974 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3129, d5974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24748 p hg
    simpa only [d3129, d5974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3129, d5974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24749 p hg
    simpa only [d3129, d5974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24751 (p : Pattern) (guard : d4985 p = 1) : d3130 p ≤ (2 : Int) + d5975 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3130, d5975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24750 p hg
    simpa only [d3130, d5975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3130, d5975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24463 p hg
    simpa only [d3130, d5975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24752 (p : Pattern) (guard : d4985 p = 1) : d3131 p ≤ (2 : Int) + d5976 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3131, d5976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24734 p hg
    simpa only [d3131, d5976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3131, d5976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3131, d5976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24753 (p : Pattern) (guard : d4985 p = 1) : d3132 p ≤ (2 : Int) + d5977 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3132, d5977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24752 p hg
    simpa only [d3132, d5977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3132, d5977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3132, d5977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24754 (p : Pattern) (guard : d4985 p = 1) : d3133 p ≤ (2 : Int) + d5978 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3133, d5978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24753 p hg
    simpa only [d3133, d5978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3133, d5978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3133, d5978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24755 (p : Pattern) (guard : d4985 p = 1) : d3134 p ≤ (2 : Int) + d5979 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3134, d5979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24751 p hg
    simpa only [d3134, d5979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3134, d5979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24754 p hg
    simpa only [d3134, d5979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24756 (p : Pattern) (guard : d4985 p = 1) : d3135 p ≤ (2 : Int) + d5980 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3135, d5980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24738 p hg
    simpa only [d3135, d5980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3135, d5980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24755 p hg
    simpa only [d3135, d5980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24757 (p : Pattern) (guard : d4985 p = 1) : d3136 p ≤ (2 : Int) + d5981 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3136, d5981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24710 p hg
    simpa only [d3136, d5981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3136, d5981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24756 p hg
    simpa only [d3136, d5981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24758 (p : Pattern) (guard : d4985 p = 1) : d3137 p ≤ (2 : Int) + d5982 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3137, d5982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24756 p hg
    simpa only [d3137, d5982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3137, d5982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3137, d5982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24759 (p : Pattern) (guard : d4985 p = 1) : d3138 p ≤ (2 : Int) + d5983 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3138, d5983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24757 p hg
    simpa only [d3138, d5983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3138, d5983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24758 p hg
    simpa only [d3138, d5983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24760 (p : Pattern) (guard : d4985 p = 1) : d3139 p ≤ (2 : Int) + d5984 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3139, d5984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24477 p hg
    simpa only [d3139, d5984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3139, d5984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24759 p hg
    simpa only [d3139, d5984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24761 (p : Pattern) (guard : d4985 p = 1) : d3140 p ≤ (2 : Int) + d5985 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3140, d5985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24480 p hg
    simpa only [d3140, d5985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3140, d5985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24760 p hg
    simpa only [d3140, d5985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24762 (p : Pattern) (guard : d4985 p = 1) : d3141 p ≤ (2 : Int) + d5986 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3141, d5986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24496 p hg
    simpa only [d3141, d5986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3141, d5986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3141, d5986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24763 (p : Pattern) (guard : d4985 p = 1) : d3142 p ≤ (2 : Int) + d5987 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3142, d5987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24547 p hg
    simpa only [d3142, d5987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3142, d5987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24762 p hg
    simpa only [d3142, d5987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24764 (p : Pattern) (guard : d4985 p = 1) : d3143 p ≤ (2 : Int) + d5988 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3143, d5988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24762 p hg
    simpa only [d3143, d5988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3143, d5988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3143, d5988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24765 (p : Pattern) (guard : d4985 p = 1) : d3144 p ≤ (2 : Int) + d5989 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3144, d5989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24763 p hg
    simpa only [d3144, d5989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3144, d5989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24764 p hg
    simpa only [d3144, d5989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24766 (p : Pattern) (guard : d4985 p = 1) : d3145 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24532 p hg
    simpa only [d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24767 (p : Pattern) (guard : d4985 p = 1) : d3146 p ≤ (2 : Int) + d5922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3146, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24556 p hg
    simpa only [d3146, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3146, d5922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24766 p hg
    simpa only [d3146, d5922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24768 (p : Pattern) (guard : d4985 p = 1) : d3147 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24766 p hg
    simpa only [d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24769 (p : Pattern) (guard : d4985 p = 1) : d3148 p ≤ (2 : Int) + d5923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3148, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24767 p hg
    simpa only [d3148, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3148, d5923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24768 p hg
    simpa only [d3148, d5923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24770 (p : Pattern) (guard : d4985 p = 1) : d3149 p ≤ (2 : Int) + d5990 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3149, d5990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24765 p hg
    simpa only [d3149, d5990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3149, d5990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24769 p hg
    simpa only [d3149, d5990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24771 (p : Pattern) (guard : d4985 p = 1) : d3150 p ≤ (2 : Int) + d5991 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3150, d5991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24538 p hg
    simpa only [d3150, d5991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3150, d5991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24770 p hg
    simpa only [d3150, d5991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24772 (p : Pattern) (guard : d4985 p = 1) : d3151 p ≤ (2 : Int) + d5992 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3151, d5992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24593 p hg
    simpa only [d3151, d5992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3151, d5992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3151, d5992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24773 (p : Pattern) (guard : d4985 p = 1) : d3152 p ≤ (2 : Int) + d5993 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3152, d5993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24610 p hg
    simpa only [d3152, d5993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3152, d5993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24772 p hg
    simpa only [d3152, d5993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24774 (p : Pattern) (guard : d4985 p = 1) : d3153 p ≤ (2 : Int) + d5994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3153, d5994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24772 p hg
    simpa only [d3153, d5994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3153, d5994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24302 p hg
    simpa only [d3153, d5994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24775 (p : Pattern) (guard : d4985 p = 1) : d3154 p ≤ (2 : Int) + d5995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3154, d5995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24773 p hg
    simpa only [d3154, d5995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3154, d5995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24774 p hg
    simpa only [d3154, d5995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24776 (p : Pattern) (guard : d4985 p = 1) : d3155 p ≤ (2 : Int) + d5996 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3155, d5996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24775 p hg
    simpa only [d3155, d5996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3155, d5996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24618 p hg
    simpa only [d3155, d5996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24777 (p : Pattern) (guard : d4985 p = 1) : d3156 p ≤ (2 : Int) + d5997 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3156, d5997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24609 p hg
    simpa only [d3156, d5997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3156, d5997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24776 p hg
    simpa only [d3156, d5997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24778 (p : Pattern) (guard : d4985 p = 1) : d3157 p ≤ (2 : Int) + d5998 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3157, d5998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24771 p hg
    simpa only [d3157, d5998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3157, d5998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24777 p hg
    simpa only [d3157, d5998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare24779 (p : Pattern) (guard : d4985 p = 1) : d3158 p ≤ (2 : Int) + d5999 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d3158, d5999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24777 p hg
    simpa only [d3158, d5999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d3158, d5999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24625 p hg
    simpa only [d3158, d5999, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
