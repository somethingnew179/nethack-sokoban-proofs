/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15680 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15681 (p : Pattern) (guard : d4475 p = 1) : d1692 p ≤ (2 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15680 p hg
    simpa only [d4475, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d4475, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15682 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15683 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  omega
theorem compare15684 (p : Pattern) (guard : d1 p = 1) : d1693 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15685 (p : Pattern) (guard : d1 p = 1) : d1694 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15684 p hg
    simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15686 (p : Pattern) (guard : d1 p = 1) : d1695 p ≤ (2 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15685 p hg
    simpa only [d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15687 (p : Pattern) (guard : d1 p = 1) : d1696 p ≤ (2 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15686 p hg
    simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15685 p hg
    simpa only [d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15688 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15689 (p : Pattern) (guard : d4474 p = 1) : d1697 p ≤ (2 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15687 p hg
    simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15688 p hg
    simpa only [d4474, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15690 (p : Pattern) (guard : d4475 p = 1) : d1698 p ≤ (2 : Int) + d18 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15682 p hg
    simpa only [d4475, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15689 p hg
    simpa only [d4475, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15691 (p : Pattern) (guard : d4475 p = 1) : d1699 p ≤ (2 : Int) + d4477 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1699, d4477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15681 p hg
    simpa only [d1699, d4477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1699, d4477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15690 p hg
    simpa only [d1699, d4477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15692 (p : Pattern) (guard : d4475 p = 1) : d1700 p ≤ (2 : Int) + d4478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1700, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15679 p hg
    simpa only [d1700, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1700, d4478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1700, d4478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15693 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (2 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15694 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  omega
theorem compare15695 (p : Pattern) (guard : d1 p = 1) : d1701 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15694 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15696 (p : Pattern) (guard : d1 p = 1) : d1702 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15695 p hg
    simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d1702, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15697 (p : Pattern) (guard : d1 p = 1) : d1703 p ≤ (2 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15696 p hg
    simpa only [d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15698 (p : Pattern) (guard : d1 p = 1) : d1704 p ≤ (2 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15697 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15696 p hg
    simpa only [d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15699 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15700 (p : Pattern) (guard : d4474 p = 1) : d1705 p ≤ (2 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15698 p hg
    simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15699 p hg
    simpa only [d4474, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15701 (p : Pattern) (guard : d4475 p = 1) : d1706 p ≤ (2 : Int) + d24 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15693 p hg
    simpa only [d4475, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15700 p hg
    simpa only [d4475, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15702 (p : Pattern) (guard : d4475 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare15703 (p : Pattern) (guard : d4475 p = 1) : d1707 p ≤ (2 : Int) + d4479 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1707, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15701 p hg
    simpa only [d1707, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1707, d4479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1707, d4479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15704 (p : Pattern) (guard : d4475 p = 1) : d1708 p ≤ (2 : Int) + d4480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1708, d4480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15691 p hg
    simpa only [d1708, d4480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1708, d4480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15703 p hg
    simpa only [d1708, d4480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15705 (p : Pattern) (guard : d4475 p = 1) : d1709 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1709, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15692 p hg
    simpa only [d1709, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1709, d4481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15704 p hg
    simpa only [d1709, d4481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15706 (p : Pattern) (guard : d0 p = 1) : d1738 p ≤ (2 : Int) + d4481 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15707 (p : Pattern) (guard : d4476 p = 1) : d1739 p ≤ (2 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15705 p hg
    simpa only [d4476, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15706 p hg
    simpa only [d4476, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15708 (p : Pattern) (guard : d0 p = 1) : d1740 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15709 (p : Pattern) (guard : d4475 p = 1) : d1741 p ≤ (2 : Int) + d14 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15708 p hg
    simpa only [d4475, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15675 p hg
    simpa only [d4475, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15710 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (2 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15711 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare15712 (p : Pattern) (guard : d1 p = 1) : d1742 p ≤ (2 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15713 (p : Pattern) (guard : d1 p = 1) : d1743 p ≤ (2 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15712 p hg
    simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d1743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15714 (p : Pattern) (guard : d1 p = 1) : d1744 p ≤ (2 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15713 p hg
    simpa only [d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15715 (p : Pattern) (guard : d1 p = 1) : d1745 p ≤ (2 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15714 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15713 p hg
    simpa only [d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15716 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15717 (p : Pattern) (guard : d4474 p = 1) : d1746 p ≤ (2 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15715 p hg
    simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15716 p hg
    simpa only [d4474, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15718 (p : Pattern) (guard : d4475 p = 1) : d1747 p ≤ (2 : Int) + d31 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15710 p hg
    simpa only [d4475, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15717 p hg
    simpa only [d4475, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15719 (p : Pattern) (guard : d4475 p = 1) : d1748 p ≤ (2 : Int) + d4482 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1748, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15709 p hg
    simpa only [d1748, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1748, d4482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15718 p hg
    simpa only [d1748, d4482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15720 (p : Pattern) (guard : d4475 p = 1) : d1749 p ≤ (2 : Int) + d4483 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1749, d4483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15690 p hg
    simpa only [d1749, d4483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1749, d4483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15701 p hg
    simpa only [d1749, d4483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15721 (p : Pattern) (guard : d4475 p = 1) : d1750 p ≤ (2 : Int) + d4484 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1750, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15719 p hg
    simpa only [d1750, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1750, d4484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15720 p hg
    simpa only [d1750, d4484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15722 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (2 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15723 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  omega
theorem compare15724 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15725 (p : Pattern) (guard : d1 p = 1) : d329 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15724 p hg
    simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d329, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15726 (p : Pattern) (guard : d1 p = 1) : d1751 p ≤ (2 : Int) + d58 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15725 p hg
    simpa only [d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15727 (p : Pattern) (guard : d1 p = 1) : d1752 p ≤ (2 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15726 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15725 p hg
    simpa only [d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15728 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15729 (p : Pattern) (guard : d4474 p = 1) : d1753 p ≤ (2 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15727 p hg
    simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d4474, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15730 (p : Pattern) (guard : d4475 p = 1) : d1754 p ≤ (2 : Int) + d58 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15722 p hg
    simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15729 p hg
    simpa only [d4475, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15731 (p : Pattern) (guard : d4475 p = 1) : d1755 p ≤ (2 : Int) + d4485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1755, d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15690 p hg
    simpa only [d1755, d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1755, d4485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15730 p hg
    simpa only [d1755, d4485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15732 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15733 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare15734 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15735 (p : Pattern) (guard : d1 p = 1) : d327 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15734 p hg
    simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d327, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15736 (p : Pattern) (guard : d1 p = 1) : d1728 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12115 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15735 p hg
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15737 (p : Pattern) (guard : d1 p = 1) : d1729 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15736 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15735 p hg
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15738 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15739 (p : Pattern) (guard : d4474 p = 1) : d1730 p ≤ (2 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15737 p hg
    simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d4474, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15740 (p : Pattern) (guard : d4475 p = 1) : d1756 p ≤ (2 : Int) + d40 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15732 p hg
    simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15739 p hg
    simpa only [d4475, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15741 (p : Pattern) (guard : d4475 p = 1) : d1757 p ≤ (2 : Int) + d4486 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1757, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15740 p hg
    simpa only [d1757, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1757, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1757, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15742 (p : Pattern) (guard : d4475 p = 1) : d1758 p ≤ (2 : Int) + d4487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1758, d4487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15731 p hg
    simpa only [d1758, d4487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1758, d4487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15741 p hg
    simpa only [d1758, d4487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15743 (p : Pattern) (guard : d4475 p = 1) : d1759 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1759, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15721 p hg
    simpa only [d1759, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1759, d4488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15742 p hg
    simpa only [d1759, d4488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15744 (p : Pattern) (guard : d0 p = 1) : d1766 p ≤ (2 : Int) + d4488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15745 (p : Pattern) (guard : d4476 p = 1) : d1767 p ≤ (2 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15743 p hg
    simpa only [d4476, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d1767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15744 p hg
    simpa only [d4476, d1767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15746 (p : Pattern) (guard : d4476 p = 1) : d1768 p ≤ (2 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d1768, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15707 p hg
    simpa only [d1768, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d1768, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15745 p hg
    simpa only [d1768, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15747 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15748 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15749 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15748 p hg
    simpa only [d1770, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d1770, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15750 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (2 : Int) + d31 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15749 p hg
    simpa only [d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15751 (p : Pattern) (guard : d1 p = 1) : d1772 p ≤ (2 : Int) + d31 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15750 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15749 p hg
    simpa only [d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15752 (p : Pattern) (guard : d4474 p = 1) : d1773 p ≤ (2 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15751 p hg
    simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15716 p hg
    simpa only [d4474, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15753 (p : Pattern) (guard : d4475 p = 1) : d1774 p ≤ (2 : Int) + d31 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15747 p hg
    simpa only [d4475, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15752 p hg
    simpa only [d4475, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15754 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15755 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) ≤ (2 : Int) + 6
  decide
theorem compare15756 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15757 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15756 p hg
    simpa only [d14, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15758 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d6 p := by
  omega
theorem compare15759 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15760 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d34 p := by
  omega
theorem compare15761 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15759 p hg
    simpa only [d1776, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15760 p hg
    simpa only [d1776, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15762 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15757 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15761 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15763 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d6 p := by
  change (4 : Int) ≤ (2 : Int) + 6
  decide
theorem compare15764 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15765 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15763 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15766 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15764 p hg
    simpa only [d1770, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15765 p hg
    simpa only [d1770, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15767 (p : Pattern) (guard : d1 p = 1) : d1778 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15755 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15768 (p : Pattern) (guard : d1 p = 1) : d1779 p ≤ (2 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1779, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15767 p hg
    simpa only [d1779, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1779, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d1779, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15769 (p : Pattern) (guard : d1 p = 1) : d1780 p ≤ (2 : Int) + d35 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15766 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15768 p hg
    simpa only [d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15770 (p : Pattern) (guard : d1 p = 1) : d1781 p ≤ (2 : Int) + d35 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15762 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15769 p hg
    simpa only [d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15771 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15772 (p : Pattern) (guard : d4474 p = 1) : d1782 p ≤ (2 : Int) + d35 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15770 p hg
    simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15771 p hg
    simpa only [d4474, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15773 (p : Pattern) (guard : d4475 p = 1) : d1783 p ≤ (2 : Int) + d35 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15754 p hg
    simpa only [d4475, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15772 p hg
    simpa only [d4475, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15774 (p : Pattern) (guard : d4475 p = 1) : d1784 p ≤ (2 : Int) + d4490 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1784, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15753 p hg
    simpa only [d1784, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1784, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15773 p hg
    simpa only [d1784, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15775 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15776 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) ≤ (2 : Int) + 11
  decide
theorem compare15777 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15778 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15777 p hg
    simpa only [d14, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15779 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15780 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15779 p hg
    simpa only [d1776, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4855 p hg
    simpa only [d1776, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15781 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15778 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15780 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15782 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15783 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15782 p hg
    simpa only [d1770, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4727 p hg
    simpa only [d1770, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15784 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15776 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15785 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d11 p := by
  change (9 : Int) ≤ (2 : Int) + 11
  decide
theorem compare15786 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15785 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15787 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15784 p hg
    simpa only [d1786, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15786 p hg
    simpa only [d1786, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15788 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d40 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15783 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15787 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15789 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d40 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15781 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15788 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15790 (p : Pattern) (guard : d4474 p = 1) : d1789 p ≤ (2 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15789 p hg
    simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15738 p hg
    simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15791 (p : Pattern) (guard : d4475 p = 1) : d1790 p ≤ (2 : Int) + d40 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15775 p hg
    simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15790 p hg
    simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15792 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15793 (p : Pattern) (guard : d1 p = 1) : d1791 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15794 (p : Pattern) (guard : d1 p = 1) : d1792 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15793 p hg
    simpa only [d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15795 (p : Pattern) (guard : d1 p = 1) : d1793 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15794 p hg
    simpa only [d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15796 (p : Pattern) (guard : d1 p = 1) : d1794 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15797 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15796 p hg
    simpa only [d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15798 (p : Pattern) (guard : d1 p = 1) : d339 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15799 (p : Pattern) (guard : d1 p = 1) : d1796 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15797 p hg
    simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15798 p hg
    simpa only [d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15800 (p : Pattern) (guard : d1 p = 1) : d1797 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15795 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15799 p hg
    simpa only [d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15801 (p : Pattern) (guard : d4474 p = 1) : d1798 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15800 p hg
    simpa only [d4474, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15802 (p : Pattern) (guard : d4475 p = 1) : d1799 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15792 p hg
    simpa only [d4475, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15801 p hg
    simpa only [d4475, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15803 (p : Pattern) (guard : d4475 p = 1) : d1800 p ≤ (2 : Int) + d4486 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1800, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15791 p hg
    simpa only [d1800, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1800, d4486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d1800, d4486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15804 (p : Pattern) (guard : d4475 p = 1) : d1801 p ≤ (2 : Int) + d4491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1801, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15774 p hg
    simpa only [d1801, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1801, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15803 p hg
    simpa only [d1801, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15805 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15806 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) ≤ (2 : Int) + 12
  decide
theorem compare15807 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15808 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15807 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15809 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15810 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15809 p hg
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15811 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15808 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15810 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15812 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15813 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15812 p hg
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15814 (p : Pattern) (guard : d1 p = 1) : d1785 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15806 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15815 (p : Pattern) (guard : d1 p = 1) : d1786 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15814 p hg
    simpa only [d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15816 (p : Pattern) (guard : d1 p = 1) : d1787 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15813 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15815 p hg
    simpa only [d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15817 (p : Pattern) (guard : d1 p = 1) : d1788 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15811 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15816 p hg
    simpa only [d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15818 (p : Pattern) (guard : d4474 p = 1) : d1789 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15817 p hg
    simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15819 (p : Pattern) (guard : d4475 p = 1) : d1790 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15805 p hg
    simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15818 p hg
    simpa only [d4475, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
