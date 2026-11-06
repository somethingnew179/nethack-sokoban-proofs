/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6580 (p : Pattern) (guard : d874 p = 1) : d610 p ≤ (1 : Int) + d1227 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6566 p hg
    simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d1227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6581 (p : Pattern) (guard : d874 p = 1) : d611 p ≤ (1 : Int) + d1228 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d611, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d611, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d611, d1228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6580 p hg
    simpa only [d611, d1228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6582 (p : Pattern) (guard : d0 p = 1) : d623 p ≤ (1 : Int) + d1228 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6583 (p : Pattern) (guard : d875 p = 1) : d624 p ≤ (1 : Int) + d1228 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6581 p hg
    simpa only [d875, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6582 p hg
    simpa only [d875, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6584 (p : Pattern) (guard : d875 p = 1) : d625 p ≤ (1 : Int) + d1501 p := by
  cases selected : p 86 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d625, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d625, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d625, d1501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6583 p hg
    simpa only [d625, d1501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6585 (p : Pattern) (guard : d873 p = 1) : d584 p ≤ (1 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d584, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6586 (p : Pattern) (guard : d873 p = 1) : d626 p ≤ (1 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6585 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6510 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6587 (p : Pattern) (guard : d873 p = 1) : d627 p ≤ (1 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d627, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6586 p hg
    simpa only [d627, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d627, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d627, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6588 (p : Pattern) (guard : d874 p = 1) : d628 p ≤ (1 : Int) + d28 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6492 p hg
    simpa only [d874, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6587 p hg
    simpa only [d874, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6589 (p : Pattern) (guard : d874 p = 1) : d629 p ≤ (1 : Int) + d28 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6590 (p : Pattern) (guard : d874 p = 1) : d630 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d630, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d630, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d630, d1224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d630, d1224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6591 (p : Pattern) (guard : d0 p = 1) : d636 p ≤ (1 : Int) + d1224 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6592 (p : Pattern) (guard : d875 p = 1) : d637 p ≤ (1 : Int) + d1224 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6590 p hg
    simpa only [d875, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6591 p hg
    simpa only [d875, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6593 (p : Pattern) (guard : d0 p = 1) : d613 p ≤ (1 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6594 (p : Pattern) (guard : d873 p = 1) : d539 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d539, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare69 p hg
    simpa only [d873, d539, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d539, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d873, d539, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6595 (p : Pattern) (guard : d873 p = 1) : d539 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6594 p hg
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6596 (p : Pattern) (guard : d873 p = 1) : d598 p ≤ (1 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d598, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6595 p hg
    simpa only [d598, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d598, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d598, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6597 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (1 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare65 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6598 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6597 p hg
    simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6599 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare67 p hg
    simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6598 p hg
    simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6600 (p : Pattern) (guard : d873 p = 1) : d545 p ≤ (1 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d545, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6599 p hg
    simpa only [d873, d545, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d545, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d873, d545, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6601 (p : Pattern) (guard : d873 p = 1) : d638 p ≤ (1 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d638, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d638, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d638, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d638, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6602 (p : Pattern) (guard : d873 p = 1) : d639 p ≤ (1 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d639, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6601 p hg
    simpa only [d639, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d639, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d639, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6603 (p : Pattern) (guard : d873 p = 1) : d640 p ≤ (1 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6602 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6604 (p : Pattern) (guard : d873 p = 1) : d545 p ≤ (1 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d545, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d873, d545, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d545, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d873, d545, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6605 (p : Pattern) (guard : d873 p = 1) : d545 p ≤ (1 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6604 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6606 (p : Pattern) (guard : d873 p = 1) : d600 p ≤ (1 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d600, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6605 p hg
    simpa only [d600, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d600, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d600, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6607 (p : Pattern) (guard : d873 p = 1) : d601 p ≤ (1 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d601, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d601, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d601, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6606 p hg
    simpa only [d601, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6608 (p : Pattern) (guard : d873 p = 1) : d641 p ≤ (1 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d641, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6603 p hg
    simpa only [d641, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d641, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6607 p hg
    simpa only [d641, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6609 (p : Pattern) (guard : d874 p = 1) : d642 p ≤ (1 : Int) + d57 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6593 p hg
    simpa only [d874, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6608 p hg
    simpa only [d874, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6610 (p : Pattern) (guard : d874 p = 1) : d643 p ≤ (1 : Int) + d1231 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d643, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d643, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d643, d1231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6609 p hg
    simpa only [d643, d1231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6611 (p : Pattern) (guard : d0 p = 1) : d619 p ≤ (1 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6612 (p : Pattern) (guard : d873 p = 1) : d576 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6613 (p : Pattern) (guard : d873 p = 1) : d578 p ≤ (1 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6614 (p : Pattern) (guard : d873 p = 1) : d586 p ≤ (1 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6612 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6613 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6615 (p : Pattern) (guard : d874 p = 1) : d644 p ≤ (1 : Int) + d2 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6611 p hg
    simpa only [d874, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6614 p hg
    simpa only [d874, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6616 (p : Pattern) (guard : d874 p = 1) : d645 p ≤ (1 : Int) + d1232 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d645, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d645, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d645, d1232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d645, d1232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6617 (p : Pattern) (guard : d874 p = 1) : d646 p ≤ (1 : Int) + d1233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d646, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6610 p hg
    simpa only [d646, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d646, d1233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6616 p hg
    simpa only [d646, d1233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6618 (p : Pattern) (guard : d0 p = 1) : d649 p ≤ (1 : Int) + d1233 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6619 (p : Pattern) (guard : d875 p = 1) : d650 p ≤ (1 : Int) + d1233 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6617 p hg
    simpa only [d875, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6618 p hg
    simpa only [d875, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6620 (p : Pattern) (guard : d875 p = 1) : d651 p ≤ (1 : Int) + d1502 p := by
  cases selected : p 86 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d651, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6592 p hg
    simpa only [d651, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d651, d1502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d651, d1502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6621 (p : Pattern) (guard : d875 p = 1) : d652 p ≤ (1 : Int) + d1503 p := by
  cases selected : p 80 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d652, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6584 p hg
    simpa only [d652, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d652, d1503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6620 p hg
    simpa only [d652, d1503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6622 (p : Pattern) (guard : d1171 p = 1) : d538 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6375 p hg
    simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6623 (p : Pattern) (guard : d1171 p = 1) : d539 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6624 (p : Pattern) (guard : d1171 p = 1) : d540 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6625 (p : Pattern) (guard : d1171 p = 1) : d541 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d541, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d541, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d541, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d541, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6626 (p : Pattern) (guard : d1171 p = 1) : d542 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d542, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d542, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d542, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d542, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6627 (p : Pattern) (guard : d1171 p = 1) : d543 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d543, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d543, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d543, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d543, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6628 (p : Pattern) (guard : d1171 p = 1) : d544 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6627 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6629 (p : Pattern) (guard : d1171 p = 1) : d545 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6630 (p : Pattern) (guard : d1171 p = 1) : d546 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6379 p hg
    simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6631 (p : Pattern) (guard : d1171 p = 1) : d547 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d547, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d547, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d547, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d547, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6632 (p : Pattern) (guard : d1171 p = 1) : d548 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d548, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d548, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d548, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d548, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6633 (p : Pattern) (guard : d1171 p = 1) : d549 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6627 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6634 (p : Pattern) (guard : d1171 p = 1) : d550 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6635 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6636 (p : Pattern) (guard : d1167 p = 1) : d31 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d1167, d31, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6637 (p : Pattern) (guard : d1171 p = 1) : d551 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6377 p hg
    simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6638 (p : Pattern) (guard : d1171 p = 1) : d552 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d552, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d552, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d552, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d552, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6639 (p : Pattern) (guard : d1171 p = 1) : d553 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d553, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d553, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d553, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d553, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6640 (p : Pattern) (guard : d1171 p = 1) : d554 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6641 (p : Pattern) (guard : d1171 p = 1) : d555 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6640 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6642 (p : Pattern) (guard : d1171 p = 1) : d556 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6641 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6643 (p : Pattern) (guard : d1171 p = 1) : d557 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6644 (p : Pattern) (guard : d1171 p = 1) : d558 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6645 (p : Pattern) (guard : d1171 p = 1) : d559 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6646 (p : Pattern) (guard : d1171 p = 1) : d560 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6645 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6647 (p : Pattern) (guard : d1171 p = 1) : d561 p ≤ (0 : Int) + d653 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6646 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6648 (p : Pattern) (guard : d1171 p = 1) : d562 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d562, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d562, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d562, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d562, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6649 (p : Pattern) (guard : d1171 p = 1) : d563 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d563, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d563, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d563, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d563, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6650 (p : Pattern) (guard : d1171 p = 1) : d564 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d564, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d564, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d564, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d564, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6651 (p : Pattern) (guard : d1171 p = 1) : d565 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d565, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d565, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d565, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6650 p hg
    simpa only [d565, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6652 (p : Pattern) (guard : d1171 p = 1) : d566 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6653 (p : Pattern) (guard : d1171 p = 1) : d567 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6654 (p : Pattern) (guard : d1171 p = 1) : d568 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d568, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d568, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d568, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d568, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6655 (p : Pattern) (guard : d1171 p = 1) : d569 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d569, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d569, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d569, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d569, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6656 (p : Pattern) (guard : d1171 p = 1) : d570 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6657 (p : Pattern) (guard : d1171 p = 1) : d571 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6656 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6658 (p : Pattern) (guard : d1171 p = 1) : d572 p ≤ (0 : Int) + d656 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6653 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6657 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6659 (p : Pattern) (guard : d1171 p = 1) : d573 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d573, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6647 p hg
    simpa only [d573, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d573, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6658 p hg
    simpa only [d573, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6660 (p : Pattern) (guard : d1171 p = 1) : d574 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d574, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d574, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d574, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d574, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6661 (p : Pattern) (guard : d1171 p = 1) : d575 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6662 (p : Pattern) (guard : d1171 p = 1) : d576 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d576, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d576, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d576, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d576, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6663 (p : Pattern) (guard : d1171 p = 1) : d577 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d577, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d577, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d577, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d577, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6664 (p : Pattern) (guard : d1171 p = 1) : d578 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d578, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d578, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d578, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d578, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6665 (p : Pattern) (guard : d1171 p = 1) : d579 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d579, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d579, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d579, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6664 p hg
    simpa only [d579, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6666 (p : Pattern) (guard : d1171 p = 1) : d580 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6665 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6667 (p : Pattern) (guard : d1171 p = 1) : d581 p ≤ (0 : Int) + d661 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d581, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d581, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d581, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d581, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6668 (p : Pattern) (guard : d1171 p = 1) : d582 p ≤ (0 : Int) + d662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d582, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d582, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d582, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d582, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6669 (p : Pattern) (guard : d1171 p = 1) : d583 p ≤ (0 : Int) + d7 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6670 (p : Pattern) (guard : d1171 p = 1) : d584 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d584, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6669 p hg
    simpa only [d584, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d584, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d584, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6671 (p : Pattern) (guard : d1171 p = 1) : d585 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6672 (p : Pattern) (guard : d1171 p = 1) : d586 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6664 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6673 (p : Pattern) (guard : d1171 p = 1) : d587 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d587, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6671 p hg
    simpa only [d587, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d587, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d587, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6674 (p : Pattern) (guard : d1171 p = 1) : d588 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d588, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d588, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d588, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d588, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6675 (p : Pattern) (guard : d1171 p = 1) : d589 p ≤ (0 : Int) + d665 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d589, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6668 p hg
    simpa only [d589, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d589, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d589, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6676 (p : Pattern) (guard : d1171 p = 1) : d590 p ≤ (0 : Int) + d666 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d590, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d590, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d590, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d590, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6677 (p : Pattern) (guard : d1171 p = 1) : d591 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d591, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d591, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d591, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d591, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6678 (p : Pattern) (guard : d1171 p = 1) : d592 p ≤ (0 : Int) + d668 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d592, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d592, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d592, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d592, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6679 (p : Pattern) (guard : d1171 p = 1) : d593 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d593, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6653 p hg
    simpa only [d593, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d593, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6678 p hg
    simpa only [d593, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6680 (p : Pattern) (guard : d1171 p = 1) : d594 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d594, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6677 p hg
    simpa only [d594, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d594, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d594, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6681 (p : Pattern) (guard : d1171 p = 1) : d595 p ≤ (0 : Int) + d671 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d595, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6675 p hg
    simpa only [d595, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d595, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d595, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6682 (p : Pattern) (guard : d1171 p = 1) : d596 p ≤ (0 : Int) + d672 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d596, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6660 p hg
    simpa only [d596, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d596, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d596, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6683 (p : Pattern) (guard : d1171 p = 1) : d597 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d597, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d597, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d597, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d597, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6684 (p : Pattern) (guard : d1171 p = 1) : d598 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d598, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d598, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d598, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d598, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6685 (p : Pattern) (guard : d1171 p = 1) : d599 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6683 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6686 (p : Pattern) (guard : d1171 p = 1) : d600 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d600, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d600, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d600, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6650 p hg
    simpa only [d600, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6687 (p : Pattern) (guard : d1171 p = 1) : d601 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6686 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6688 (p : Pattern) (guard : d1171 p = 1) : d602 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6685 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6689 (p : Pattern) (guard : d1171 p = 1) : d603 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d603, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6669 p hg
    simpa only [d603, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d603, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d603, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6690 (p : Pattern) (guard : d1171 p = 1) : d604 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d604, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d604, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d604, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d604, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6691 (p : Pattern) (guard : d1171 p = 1) : d605 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6689 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6690 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6692 (p : Pattern) (guard : d1171 p = 1) : d606 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6693 (p : Pattern) (guard : d1171 p = 1) : d607 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6688 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6692 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6694 (p : Pattern) (guard : d1171 p = 1) : d608 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d608, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d608, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d608, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6693 p hg
    simpa only [d608, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6695 (p : Pattern) (guard : d1171 p = 1) : d609 p ≤ (0 : Int) + d660 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6696 (p : Pattern) (guard : d1171 p = 1) : d610 p ≤ (0 : Int) + d660 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6695 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6697 (p : Pattern) (guard : d1171 p = 1) : d611 p ≤ (0 : Int) + d675 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d611, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6694 p hg
    simpa only [d611, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d611, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d611, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6698 (p : Pattern) (guard : d1171 p = 1) : d612 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6689 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6699 (p : Pattern) (guard : d1171 p = 1) : d613 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6698 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6700 (p : Pattern) (guard : d1171 p = 1) : d614 p ≤ (0 : Int) + d676 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d614, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d614, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d614, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d614, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6701 (p : Pattern) (guard : d1171 p = 1) : d615 p ≤ (0 : Int) + d677 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d615, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d615, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d615, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d615, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6702 (p : Pattern) (guard : d1171 p = 1) : d616 p ≤ (0 : Int) + d678 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d616, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d616, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d616, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6701 p hg
    simpa only [d616, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6703 (p : Pattern) (guard : d1171 p = 1) : d617 p ≤ (0 : Int) + d679 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d617, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d617, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d617, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d617, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6704 (p : Pattern) (guard : d1171 p = 1) : d618 p ≤ (0 : Int) + d680 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d618, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6695 p hg
    simpa only [d618, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d618, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6703 p hg
    simpa only [d618, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6705 (p : Pattern) (guard : d1171 p = 1) : d619 p ≤ (0 : Int) + d659 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6706 (p : Pattern) (guard : d1171 p = 1) : d620 p ≤ (0 : Int) + d681 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d620, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d620, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d620, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d620, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6707 (p : Pattern) (guard : d1171 p = 1) : d621 p ≤ (0 : Int) + d682 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d621, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d621, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d621, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d621, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6708 (p : Pattern) (guard : d1171 p = 1) : d622 p ≤ (0 : Int) + d683 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d622, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6704 p hg
    simpa only [d622, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d622, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6707 p hg
    simpa only [d622, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6709 (p : Pattern) (guard : d1171 p = 1) : d623 p ≤ (0 : Int) + d684 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d623, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6702 p hg
    simpa only [d623, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d623, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6708 p hg
    simpa only [d623, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6710 (p : Pattern) (guard : d1171 p = 1) : d624 p ≤ (0 : Int) + d685 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d624, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6697 p hg
    simpa only [d624, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d624, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d624, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6711 (p : Pattern) (guard : d1171 p = 1) : d625 p ≤ (0 : Int) + d686 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d625, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6682 p hg
    simpa only [d625, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d625, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d625, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6712 (p : Pattern) (guard : d1171 p = 1) : d626 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6713 (p : Pattern) (guard : d1171 p = 1) : d627 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6714 (p : Pattern) (guard : d1171 p = 1) : d628 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6713 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6715 (p : Pattern) (guard : d1171 p = 1) : d629 p ≤ (0 : Int) + d654 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6716 (p : Pattern) (guard : d1171 p = 1) : d630 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d630, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d630, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d630, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d630, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6717 (p : Pattern) (guard : d1171 p = 1) : d631 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6627 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6718 (p : Pattern) (guard : d1171 p = 1) : d632 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6717 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6719 (p : Pattern) (guard : d1171 p = 1) : d633 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d633, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d633, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d633, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d633, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
