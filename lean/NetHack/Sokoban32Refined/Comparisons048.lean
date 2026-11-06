/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6720 (p : Pattern) (guard : d1171 p = 1) : d634 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d634, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6718 p hg
    simpa only [d634, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d634, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6719 p hg
    simpa only [d634, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6721 (p : Pattern) (guard : d1171 p = 1) : d635 p ≤ (0 : Int) + d664 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6722 (p : Pattern) (guard : d1171 p = 1) : d636 p ≤ (0 : Int) + d687 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d636, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6721 p hg
    simpa only [d636, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d636, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d636, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6723 (p : Pattern) (guard : d1171 p = 1) : d637 p ≤ (0 : Int) + d688 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d637, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6716 p hg
    simpa only [d637, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d637, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6722 p hg
    simpa only [d637, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6724 (p : Pattern) (guard : d1171 p = 1) : d638 p ≤ (0 : Int) + d7 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6725 (p : Pattern) (guard : d1171 p = 1) : d639 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d639, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6724 p hg
    simpa only [d639, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d639, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d639, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6726 (p : Pattern) (guard : d1171 p = 1) : d640 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6725 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6727 (p : Pattern) (guard : d1171 p = 1) : d641 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6726 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6728 (p : Pattern) (guard : d1171 p = 1) : d642 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6729 (p : Pattern) (guard : d1171 p = 1) : d643 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d643, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d643, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d643, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6728 p hg
    simpa only [d643, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6730 (p : Pattern) (guard : d1171 p = 1) : d644 p ≤ (0 : Int) + d659 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6731 (p : Pattern) (guard : d1171 p = 1) : d645 p ≤ (0 : Int) + d689 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d645, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d645, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d645, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6730 p hg
    simpa only [d645, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6732 (p : Pattern) (guard : d1171 p = 1) : d646 p ≤ (0 : Int) + d690 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d646, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6729 p hg
    simpa only [d646, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d646, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6731 p hg
    simpa only [d646, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6733 (p : Pattern) (guard : d1171 p = 1) : d647 p ≤ (0 : Int) + d691 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d647, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6720 p hg
    simpa only [d647, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d647, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d647, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6734 (p : Pattern) (guard : d1171 p = 1) : d648 p ≤ (0 : Int) + d692 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d648, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6707 p hg
    simpa only [d648, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d648, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d648, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6735 (p : Pattern) (guard : d1171 p = 1) : d649 p ≤ (0 : Int) + d693 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d649, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6733 p hg
    simpa only [d649, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d649, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6734 p hg
    simpa only [d649, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6736 (p : Pattern) (guard : d1171 p = 1) : d650 p ≤ (0 : Int) + d694 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d650, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d650, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d650, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6735 p hg
    simpa only [d650, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6737 (p : Pattern) (guard : d1171 p = 1) : d651 p ≤ (0 : Int) + d695 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d651, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6723 p hg
    simpa only [d651, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d651, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6736 p hg
    simpa only [d651, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6738 (p : Pattern) (guard : d1171 p = 1) : d652 p ≤ (0 : Int) + d696 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d652, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6711 p hg
    simpa only [d652, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d652, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6737 p hg
    simpa only [d652, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6739 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6740 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d917, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6741 (p : Pattern) (guard : d1505 p = 1) : d6 p ≤ (0 : Int) + d3 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1505, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6740 p hg
    simpa only [d1505, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6742 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6743 (p : Pattern) (guard : d1506 p = 1) : d538 p ≤ (0 : Int) + d3 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6741 p hg
    simpa only [d1506, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6742 p hg
    simpa only [d1506, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6744 (p : Pattern) (guard : d1506 p = 1) : d539 p ≤ (0 : Int) + d3 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6741 p hg
    simpa only [d1506, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d1506, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6745 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6746 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d9 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d917, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6747 (p : Pattern) (guard : d1505 p = 1) : d12 p ≤ (0 : Int) + d9 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6745 p hg
    simpa only [d1505, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6746 p hg
    simpa only [d1505, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6748 (p : Pattern) (guard : d1506 p = 1) : d540 p ≤ (0 : Int) + d9 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6747 p hg
    simpa only [d1506, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d1506, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6749 (p : Pattern) (guard : d1506 p = 1) : d541 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d541, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d541, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d541, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d541, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6750 (p : Pattern) (guard : d1506 p = 1) : d542 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d542, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d542, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d542, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d542, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6751 (p : Pattern) (guard : d1506 p = 1) : d543 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d543, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d543, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d543, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d543, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6752 (p : Pattern) (guard : d1506 p = 1) : d544 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6750 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6753 (p : Pattern) (guard : d1505 p = 1) : d18 p ≤ (0 : Int) + d3 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1505, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d1505, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6754 (p : Pattern) (guard : d1506 p = 1) : d545 p ≤ (0 : Int) + d3 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6753 p hg
    simpa only [d1506, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d1506, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6755 (p : Pattern) (guard : d1505 p = 1) : d22 p ≤ (0 : Int) + d9 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6745 p hg
    simpa only [d1505, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare975 p hg
    simpa only [d1505, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6756 (p : Pattern) (guard : d1506 p = 1) : d546 p ≤ (0 : Int) + d9 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6755 p hg
    simpa only [d1506, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d1506, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6757 (p : Pattern) (guard : d1506 p = 1) : d547 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d547, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d547, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d547, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d547, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6758 (p : Pattern) (guard : d1506 p = 1) : d548 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d548, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d548, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d548, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6757 p hg
    simpa only [d548, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6759 (p : Pattern) (guard : d1506 p = 1) : d549 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6760 (p : Pattern) (guard : d1506 p = 1) : d550 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6752 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6761 (p : Pattern) (guard : d1505 p = 1) : d31 p ≤ (0 : Int) + d3 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d1505, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare985 p hg
    simpa only [d1505, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6762 (p : Pattern) (guard : d1506 p = 1) : d551 p ≤ (0 : Int) + d3 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6761 p hg
    simpa only [d1506, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d1506, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6763 (p : Pattern) (guard : d1506 p = 1) : d552 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d552, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d552, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d552, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d552, d1507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6764 (p : Pattern) (guard : d1506 p = 1) : d553 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d553, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d553, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d553, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d553, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6765 (p : Pattern) (guard : d1506 p = 1) : d554 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6750 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6764 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6766 (p : Pattern) (guard : d1506 p = 1) : d555 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6765 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6767 (p : Pattern) (guard : d1506 p = 1) : d556 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6766 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6768 (p : Pattern) (guard : d1506 p = 1) : d557 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6757 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6769 (p : Pattern) (guard : d1506 p = 1) : d558 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6768 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6770 (p : Pattern) (guard : d1506 p = 1) : d559 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6771 (p : Pattern) (guard : d1506 p = 1) : d560 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6770 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6768 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6772 (p : Pattern) (guard : d1506 p = 1) : d561 p ≤ (0 : Int) + d1507 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6769 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6771 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6773 (p : Pattern) (guard : d1506 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare6774 (p : Pattern) (guard : d1506 p = 1) : d562 p ≤ (0 : Int) + d1509 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d562, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d562, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d562, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d562, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6775 (p : Pattern) (guard : d1506 p = 1) : d563 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d563, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d563, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d563, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d563, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6776 (p : Pattern) (guard : d1506 p = 1) : d564 p ≤ (0 : Int) + d1509 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d564, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d564, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d564, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d564, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6777 (p : Pattern) (guard : d1506 p = 1) : d565 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d565, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6757 p hg
    simpa only [d565, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d565, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6776 p hg
    simpa only [d565, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6778 (p : Pattern) (guard : d1506 p = 1) : d566 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6775 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6777 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6779 (p : Pattern) (guard : d1506 p = 1) : d567 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6775 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6778 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6780 (p : Pattern) (guard : d1506 p = 1) : d568 p ≤ (0 : Int) + d1509 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6781 (p : Pattern) (guard : d1506 p = 1) : d569 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6763 p hg
    simpa only [d569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6782 (p : Pattern) (guard : d1506 p = 1) : d570 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6775 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6781 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6783 (p : Pattern) (guard : d1506 p = 1) : d571 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6782 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6778 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6784 (p : Pattern) (guard : d1506 p = 1) : d572 p ≤ (0 : Int) + d1510 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6779 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6783 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6785 (p : Pattern) (guard : d1506 p = 1) : d573 p ≤ (0 : Int) + d1511 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d573, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6772 p hg
    simpa only [d573, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d573, d1511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6784 p hg
    simpa only [d573, d1511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6786 (p : Pattern) (guard : d1506 p = 1) : d574 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d574, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d574, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d574, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d574, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6787 (p : Pattern) (guard : d1506 p = 1) : d575 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6750 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6788 (p : Pattern) (guard : d1506 p = 1) : d576 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d576, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d576, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d576, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d576, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6789 (p : Pattern) (guard : d1506 p = 1) : d577 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d577, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6748 p hg
    simpa only [d577, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d577, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6788 p hg
    simpa only [d577, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6790 (p : Pattern) (guard : d1506 p = 1) : d578 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d578, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d578, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d578, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d578, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6791 (p : Pattern) (guard : d1506 p = 1) : d579 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d579, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6756 p hg
    simpa only [d579, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d579, d1514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6790 p hg
    simpa only [d579, d1514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6792 (p : Pattern) (guard : d1506 p = 1) : d580 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6791 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6793 (p : Pattern) (guard : d1506 p = 1) : d581 p ≤ (0 : Int) + d1515 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d581, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6787 p hg
    simpa only [d581, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d581, d1515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d581, d1515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6794 (p : Pattern) (guard : d1506 p = 1) : d582 p ≤ (0 : Int) + d1516 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d582, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d582, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d582, d1516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6793 p hg
    simpa only [d582, d1516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6795 (p : Pattern) (guard : d1506 p = 1) : d583 p ≤ (0 : Int) + d3 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6796 (p : Pattern) (guard : d1506 p = 1) : d584 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d584, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6795 p hg
    simpa only [d584, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d584, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6749 p hg
    simpa only [d584, d1508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6797 (p : Pattern) (guard : d1506 p = 1) : d585 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6796 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6758 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6798 (p : Pattern) (guard : d1506 p = 1) : d586 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6788 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6790 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6799 (p : Pattern) (guard : d1506 p = 1) : d587 p ≤ (0 : Int) + d1517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d587, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6797 p hg
    simpa only [d587, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d587, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d587, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6800 (p : Pattern) (guard : d1506 p = 1) : d588 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d588, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d588, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d588, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6799 p hg
    simpa only [d588, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6801 (p : Pattern) (guard : d1506 p = 1) : d589 p ≤ (0 : Int) + d1519 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d589, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6794 p hg
    simpa only [d589, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d589, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d589, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6802 (p : Pattern) (guard : d1506 p = 1) : d590 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d590, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6768 p hg
    simpa only [d590, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d590, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d590, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6803 (p : Pattern) (guard : d1506 p = 1) : d591 p ≤ (0 : Int) + d1521 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d591, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6769 p hg
    simpa only [d591, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d591, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6802 p hg
    simpa only [d591, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6804 (p : Pattern) (guard : d1506 p = 1) : d592 p ≤ (0 : Int) + d1522 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d592, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6778 p hg
    simpa only [d592, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d592, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d592, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6805 (p : Pattern) (guard : d1506 p = 1) : d593 p ≤ (0 : Int) + d1523 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d593, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6779 p hg
    simpa only [d593, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d593, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6804 p hg
    simpa only [d593, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6806 (p : Pattern) (guard : d1506 p = 1) : d594 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d594, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6803 p hg
    simpa only [d594, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d594, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6805 p hg
    simpa only [d594, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6807 (p : Pattern) (guard : d1506 p = 1) : d595 p ≤ (0 : Int) + d1525 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d595, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6801 p hg
    simpa only [d595, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d595, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6806 p hg
    simpa only [d595, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6808 (p : Pattern) (guard : d1506 p = 1) : d596 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d596, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6786 p hg
    simpa only [d596, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d596, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6807 p hg
    simpa only [d596, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6809 (p : Pattern) (guard : d1506 p = 1) : d597 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d597, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6743 p hg
    simpa only [d597, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d597, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d597, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6810 (p : Pattern) (guard : d1506 p = 1) : d598 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d598, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6744 p hg
    simpa only [d598, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d598, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d598, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6811 (p : Pattern) (guard : d1506 p = 1) : d599 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6809 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6812 (p : Pattern) (guard : d1506 p = 1) : d600 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d600, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d600, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d600, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6776 p hg
    simpa only [d600, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6813 (p : Pattern) (guard : d1506 p = 1) : d601 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6812 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6814 (p : Pattern) (guard : d1506 p = 1) : d602 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6811 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6815 (p : Pattern) (guard : d1506 p = 1) : d603 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d603, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6795 p hg
    simpa only [d603, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d603, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d603, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6816 (p : Pattern) (guard : d1506 p = 1) : d604 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d604, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d604, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d604, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d604, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6817 (p : Pattern) (guard : d1506 p = 1) : d605 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6815 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6816 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6818 (p : Pattern) (guard : d1506 p = 1) : d606 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6817 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6819 (p : Pattern) (guard : d1506 p = 1) : d607 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6814 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6818 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6820 (p : Pattern) (guard : d1506 p = 1) : d608 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d608, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d608, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d608, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6819 p hg
    simpa only [d608, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6821 (p : Pattern) (guard : d1506 p = 1) : d609 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6822 (p : Pattern) (guard : d1506 p = 1) : d610 p ≤ (0 : Int) + d1514 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6823 (p : Pattern) (guard : d1506 p = 1) : d611 p ≤ (0 : Int) + d1529 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d611, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6820 p hg
    simpa only [d611, d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d611, d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6822 p hg
    simpa only [d611, d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6824 (p : Pattern) (guard : d1506 p = 1) : d612 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6815 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6825 (p : Pattern) (guard : d1506 p = 1) : d613 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6824 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6826 (p : Pattern) (guard : d1506 p = 1) : d614 p ≤ (0 : Int) + d1530 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d614, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d614, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d614, d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d614, d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6827 (p : Pattern) (guard : d1506 p = 1) : d615 p ≤ (0 : Int) + d1531 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d615, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6825 p hg
    simpa only [d615, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d615, d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6826 p hg
    simpa only [d615, d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6828 (p : Pattern) (guard : d1506 p = 1) : d616 p ≤ (0 : Int) + d1532 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d616, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d616, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d616, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6827 p hg
    simpa only [d616, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6829 (p : Pattern) (guard : d1506 p = 1) : d617 p ≤ (0 : Int) + d1533 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d617, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6792 p hg
    simpa only [d617, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d617, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d617, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6830 (p : Pattern) (guard : d1506 p = 1) : d618 p ≤ (0 : Int) + d1534 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d618, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6821 p hg
    simpa only [d618, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d618, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6829 p hg
    simpa only [d618, d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6831 (p : Pattern) (guard : d1506 p = 1) : d619 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6788 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6832 (p : Pattern) (guard : d1506 p = 1) : d620 p ≤ (0 : Int) + d1535 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d620, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d620, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d620, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6773 p hg
    simpa only [d620, d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6833 (p : Pattern) (guard : d1506 p = 1) : d621 p ≤ (0 : Int) + d1536 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d621, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6831 p hg
    simpa only [d621, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d621, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6832 p hg
    simpa only [d621, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6834 (p : Pattern) (guard : d1506 p = 1) : d622 p ≤ (0 : Int) + d1537 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d622, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6830 p hg
    simpa only [d622, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d622, d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6833 p hg
    simpa only [d622, d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6835 (p : Pattern) (guard : d1506 p = 1) : d623 p ≤ (0 : Int) + d1538 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d623, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6828 p hg
    simpa only [d623, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d623, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6834 p hg
    simpa only [d623, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6836 (p : Pattern) (guard : d1506 p = 1) : d624 p ≤ (0 : Int) + d1539 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d624, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d624, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d624, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6835 p hg
    simpa only [d624, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6837 (p : Pattern) (guard : d1506 p = 1) : d625 p ≤ (0 : Int) + d1540 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d625, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6808 p hg
    simpa only [d625, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d625, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6836 p hg
    simpa only [d625, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6838 (p : Pattern) (guard : d1506 p = 1) : d626 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6796 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6764 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6839 (p : Pattern) (guard : d1506 p = 1) : d627 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6838 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6840 (p : Pattern) (guard : d1506 p = 1) : d628 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6839 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6841 (p : Pattern) (guard : d1506 p = 1) : d629 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6840 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6842 (p : Pattern) (guard : d1506 p = 1) : d630 p ≤ (0 : Int) + d1512 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d630, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6841 p hg
    simpa only [d630, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d630, d1512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6785 p hg
    simpa only [d630, d1512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6843 (p : Pattern) (guard : d1506 p = 1) : d631 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6796 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6751 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6844 (p : Pattern) (guard : d1506 p = 1) : d632 p ≤ (0 : Int) + d1508 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6843 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6845 (p : Pattern) (guard : d1506 p = 1) : d633 p ≤ (0 : Int) + d1517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d633, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6759 p hg
    simpa only [d633, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d633, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d633, d1517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6846 (p : Pattern) (guard : d1506 p = 1) : d634 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d634, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6844 p hg
    simpa only [d634, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d634, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6845 p hg
    simpa only [d634, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6847 (p : Pattern) (guard : d1506 p = 1) : d635 p ≤ (0 : Int) + d1518 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6846 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6848 (p : Pattern) (guard : d1506 p = 1) : d636 p ≤ (0 : Int) + d1541 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d636, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6847 p hg
    simpa only [d636, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d636, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6806 p hg
    simpa only [d636, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6849 (p : Pattern) (guard : d1506 p = 1) : d637 p ≤ (0 : Int) + d1542 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d637, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6842 p hg
    simpa only [d637, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d637, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6848 p hg
    simpa only [d637, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6850 (p : Pattern) (guard : d1506 p = 1) : d638 p ≤ (0 : Int) + d3 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6762 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6851 (p : Pattern) (guard : d1506 p = 1) : d639 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d639, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d639, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d639, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6780 p hg
    simpa only [d639, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6852 (p : Pattern) (guard : d1506 p = 1) : d640 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6810 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6851 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6853 (p : Pattern) (guard : d1506 p = 1) : d641 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6852 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6813 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6854 (p : Pattern) (guard : d1506 p = 1) : d642 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6825 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6853 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6855 (p : Pattern) (guard : d1506 p = 1) : d643 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d643, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6840 p hg
    simpa only [d643, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d643, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6854 p hg
    simpa only [d643, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6856 (p : Pattern) (guard : d1506 p = 1) : d644 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6831 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6798 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6857 (p : Pattern) (guard : d1506 p = 1) : d645 p ≤ (0 : Int) + d1543 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d645, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6822 p hg
    simpa only [d645, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d645, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6856 p hg
    simpa only [d645, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6858 (p : Pattern) (guard : d1506 p = 1) : d646 p ≤ (0 : Int) + d1544 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d646, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6855 p hg
    simpa only [d646, d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d646, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6857 p hg
    simpa only [d646, d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6859 (p : Pattern) (guard : d1506 p = 1) : d647 p ≤ (0 : Int) + d1545 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d647, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6846 p hg
    simpa only [d647, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d647, d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6805 p hg
    simpa only [d647, d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
