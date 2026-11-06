/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7420 (p : Pattern) (guard : d1412 p = 1) : d655 p ≤ (2 : Int) + d1618 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d655, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d655, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d655, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d655, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7421 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1619 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d656, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d656, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d656, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7420 p hg
    simpa only [d656, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7422 (p : Pattern) (guard : d1412 p = 1) : d655 p ≤ (2 : Int) + d1620 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d655, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d655, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d655, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d655, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7423 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1621 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d656, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7401 p hg
    simpa only [d656, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d656, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7422 p hg
    simpa only [d656, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7424 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1622 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7421 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7423 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7425 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1623 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7421 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7426 (p : Pattern) (guard : d1412 p = 1) : d655 p ≤ (2 : Int) + d1624 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d655, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d655, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d655, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d655, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7427 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1625 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d656, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7409 p hg
    simpa only [d656, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d656, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7426 p hg
    simpa only [d656, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7428 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1626 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7421 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7427 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7429 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1627 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7428 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7430 (p : Pattern) (guard : d1412 p = 1) : d656 p ≤ (2 : Int) + d1628 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7425 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7431 (p : Pattern) (guard : d1412 p = 1) : d657 p ≤ (2 : Int) + d1629 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d657, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7418 p hg
    simpa only [d657, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d657, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7430 p hg
    simpa only [d657, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7432 (p : Pattern) (guard : d1412 p = 1) : d658 p ≤ (2 : Int) + d1630 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d658, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7413 p hg
    simpa only [d658, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d658, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7431 p hg
    simpa only [d658, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7433 (p : Pattern) (guard : d1412 p = 1) : d659 p ≤ (2 : Int) + d1631 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d659, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7390 p hg
    simpa only [d659, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d659, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d659, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7434 (p : Pattern) (guard : d1412 p = 1) : d660 p ≤ (2 : Int) + d1632 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d660, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7390 p hg
    simpa only [d660, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d660, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7433 p hg
    simpa only [d660, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7435 (p : Pattern) (guard : d1412 p = 1) : d659 p ≤ (2 : Int) + d1633 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d659, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d659, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d659, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d659, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7436 (p : Pattern) (guard : d1412 p = 1) : d660 p ≤ (2 : Int) + d1634 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d660, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d660, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d660, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7435 p hg
    simpa only [d660, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7437 (p : Pattern) (guard : d1412 p = 1) : d660 p ≤ (2 : Int) + d1635 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7434 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7438 (p : Pattern) (guard : d1412 p = 1) : d661 p ≤ (2 : Int) + d1636 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d661, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d661, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d661, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d661, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7439 (p : Pattern) (guard : d1412 p = 1) : d662 p ≤ (2 : Int) + d1637 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d662, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7404 p hg
    simpa only [d662, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d662, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7438 p hg
    simpa only [d662, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7440 (p : Pattern) (guard : d1412 p = 1) : d659 p ≤ (2 : Int) + d1638 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7433 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7435 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7441 (p : Pattern) (guard : d1412 p = 1) : d663 p ≤ (2 : Int) + d1639 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d663, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d663, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d663, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d663, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7442 (p : Pattern) (guard : d1412 p = 1) : d664 p ≤ (2 : Int) + d1640 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d664, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7404 p hg
    simpa only [d664, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d664, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7441 p hg
    simpa only [d664, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7443 (p : Pattern) (guard : d1412 p = 1) : d665 p ≤ (2 : Int) + d1641 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d665, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d665, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d665, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d665, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7444 (p : Pattern) (guard : d1412 p = 1) : d666 p ≤ (2 : Int) + d1642 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d666, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d666, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d666, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d666, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7445 (p : Pattern) (guard : d1412 p = 1) : d667 p ≤ (2 : Int) + d1643 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d667, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7415 p hg
    simpa only [d667, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d667, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7444 p hg
    simpa only [d667, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7446 (p : Pattern) (guard : d1412 p = 1) : d668 p ≤ (2 : Int) + d1644 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d668, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d668, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d668, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d668, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7447 (p : Pattern) (guard : d1412 p = 1) : d669 p ≤ (2 : Int) + d1645 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d669, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7425 p hg
    simpa only [d669, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d669, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7446 p hg
    simpa only [d669, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7448 (p : Pattern) (guard : d1412 p = 1) : d670 p ≤ (2 : Int) + d1646 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d670, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7445 p hg
    simpa only [d670, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d670, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7447 p hg
    simpa only [d670, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7449 (p : Pattern) (guard : d1412 p = 1) : d671 p ≤ (2 : Int) + d1647 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d671, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7443 p hg
    simpa only [d671, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d671, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7448 p hg
    simpa only [d671, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7450 (p : Pattern) (guard : d1412 p = 1) : d672 p ≤ (2 : Int) + d1648 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d672, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7432 p hg
    simpa only [d672, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d672, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7449 p hg
    simpa only [d672, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7451 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d673, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d673, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d673, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7420 p hg
    simpa only [d673, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7452 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d673, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d673, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d673, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7422 p hg
    simpa only [d673, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7453 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1651 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7452 p hg
    simpa only [d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7454 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1652 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7455 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1653 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d673, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d673, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d673, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7426 p hg
    simpa only [d673, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7456 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7455 p hg
    simpa only [d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7457 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1655 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7458 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1656 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7454 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7457 p hg
    simpa only [d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7459 (p : Pattern) (guard : d1412 p = 1) : d674 p ≤ (2 : Int) + d1657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d674, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7413 p hg
    simpa only [d674, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d674, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7458 p hg
    simpa only [d674, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7460 (p : Pattern) (guard : d1412 p = 1) : d660 p ≤ (2 : Int) + d1658 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7434 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7461 (p : Pattern) (guard : d1412 p = 1) : d660 p ≤ (2 : Int) + d1659 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7460 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7462 (p : Pattern) (guard : d1412 p = 1) : d675 p ≤ (2 : Int) + d1660 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d675, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7459 p hg
    simpa only [d675, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d675, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d675, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7463 (p : Pattern) (guard : d1412 p = 1) : d676 p ≤ (2 : Int) + d1661 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d676, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d676, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d676, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d676, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7464 (p : Pattern) (guard : d1412 p = 1) : d677 p ≤ (2 : Int) + d1662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d677, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7454 p hg
    simpa only [d677, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d677, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7463 p hg
    simpa only [d677, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7465 (p : Pattern) (guard : d1412 p = 1) : d678 p ≤ (2 : Int) + d1663 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d678, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d678, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d678, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7464 p hg
    simpa only [d678, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7466 (p : Pattern) (guard : d1412 p = 1) : d679 p ≤ (2 : Int) + d1664 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d679, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d679, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d679, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d679, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7467 (p : Pattern) (guard : d1412 p = 1) : d680 p ≤ (2 : Int) + d1665 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d680, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7460 p hg
    simpa only [d680, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d680, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7466 p hg
    simpa only [d680, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7468 (p : Pattern) (guard : d1412 p = 1) : d659 p ≤ (2 : Int) + d1666 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7433 p hg
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7469 (p : Pattern) (guard : d1412 p = 1) : d681 p ≤ (2 : Int) + d1667 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d681, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d681, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d681, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d681, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7470 (p : Pattern) (guard : d1412 p = 1) : d682 p ≤ (2 : Int) + d1668 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d682, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7468 p hg
    simpa only [d682, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d682, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7469 p hg
    simpa only [d682, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7471 (p : Pattern) (guard : d1412 p = 1) : d683 p ≤ (2 : Int) + d1669 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d683, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7467 p hg
    simpa only [d683, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d683, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d683, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7472 (p : Pattern) (guard : d1412 p = 1) : d684 p ≤ (2 : Int) + d1670 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d684, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7465 p hg
    simpa only [d684, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d684, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7471 p hg
    simpa only [d684, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7473 (p : Pattern) (guard : d1412 p = 1) : d685 p ≤ (2 : Int) + d1671 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d685, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7462 p hg
    simpa only [d685, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d685, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7472 p hg
    simpa only [d685, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7474 (p : Pattern) (guard : d1412 p = 1) : d686 p ≤ (2 : Int) + d1672 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d686, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7450 p hg
    simpa only [d686, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d686, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7473 p hg
    simpa only [d686, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7475 (p : Pattern) (guard : d1412 p = 1) : d687 p ≤ (2 : Int) + d1673 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d687, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d687, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d687, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7448 p hg
    simpa only [d687, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7476 (p : Pattern) (guard : d1412 p = 1) : d688 p ≤ (2 : Int) + d1674 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d688, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7432 p hg
    simpa only [d688, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d688, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7475 p hg
    simpa only [d688, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7477 (p : Pattern) (guard : d1412 p = 1) : d7 p ≤ (2 : Int) + d1675 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7478 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d673, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7477 p hg
    simpa only [d673, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d673, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7426 p hg
    simpa only [d673, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7479 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1677 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7478 p hg
    simpa only [d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7480 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1678 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7479 p hg
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7481 (p : Pattern) (guard : d1412 p = 1) : d673 p ≤ (2 : Int) + d1679 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7454 p hg
    simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7482 (p : Pattern) (guard : d1412 p = 1) : d674 p ≤ (2 : Int) + d1680 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d674, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7413 p hg
    simpa only [d674, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d674, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7481 p hg
    simpa only [d674, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7483 (p : Pattern) (guard : d1412 p = 1) : d659 p ≤ (2 : Int) + d1681 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7468 p hg
    simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7484 (p : Pattern) (guard : d1412 p = 1) : d689 p ≤ (2 : Int) + d1682 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d689, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d689, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d689, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7483 p hg
    simpa only [d689, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7485 (p : Pattern) (guard : d1412 p = 1) : d690 p ≤ (2 : Int) + d1683 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d690, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7482 p hg
    simpa only [d690, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d690, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7484 p hg
    simpa only [d690, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7486 (p : Pattern) (guard : d1412 p = 1) : d691 p ≤ (2 : Int) + d1684 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d691, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d691, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d691, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7447 p hg
    simpa only [d691, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7487 (p : Pattern) (guard : d1412 p = 1) : d692 p ≤ (2 : Int) + d1685 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d692, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d692, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d692, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d692, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7488 (p : Pattern) (guard : d1412 p = 1) : d693 p ≤ (2 : Int) + d1686 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d693, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7486 p hg
    simpa only [d693, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d693, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7487 p hg
    simpa only [d693, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7489 (p : Pattern) (guard : d1412 p = 1) : d694 p ≤ (2 : Int) + d1687 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d694, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7485 p hg
    simpa only [d694, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d694, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7488 p hg
    simpa only [d694, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7490 (p : Pattern) (guard : d1412 p = 1) : d695 p ≤ (2 : Int) + d1688 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d695, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7476 p hg
    simpa only [d695, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d695, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7489 p hg
    simpa only [d695, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7491 (p : Pattern) (guard : d1412 p = 1) : d696 p ≤ (2 : Int) + d1689 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d696, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d696, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d696, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7490 p hg
    simpa only [d696, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7492 (p : Pattern) (guard : d0 p = 1) : d654 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7493 (p : Pattern) (guard : d1250 p = 1) : d654 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7494 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d1240, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1240, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7495 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7494 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4099 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7496 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4101 p hg
    simpa only [d1240, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1240, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7497 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7496 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7498 (p : Pattern) (guard : d1240 p = 1) : d653 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7499 (p : Pattern) (guard : d1240 p = 1) : d654 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7498 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7500 (p : Pattern) (guard : d1253 p = 1) : d654 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7499 p hg
    simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7501 (p : Pattern) (guard : d1254 p = 1) : d654 p ≤ (0 : Int) + d328 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7500 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7502 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7494 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7503 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7496 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7504 (p : Pattern) (guard : d1240 p = 1) : d653 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d653, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d653, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d653, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d653, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7505 (p : Pattern) (guard : d1240 p = 1) : d654 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d654, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d654, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d654, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7504 p hg
    simpa only [d654, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7506 (p : Pattern) (guard : d1253 p = 1) : d654 p ≤ (0 : Int) + d329 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7505 p hg
    simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7507 (p : Pattern) (guard : d1254 p = 1) : d654 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7506 p hg
    simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7508 (p : Pattern) (guard : d1254 p = 1) : d654 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7507 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7509 (p : Pattern) (guard : d1250 p = 1) : d653 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7510 (p : Pattern) (guard : d1253 p = 1) : d653 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7498 p hg
    simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7511 (p : Pattern) (guard : d1254 p = 1) : d653 p ≤ (0 : Int) + d332 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7510 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7512 (p : Pattern) (guard : d1253 p = 1) : d653 p ≤ (0 : Int) + d333 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7504 p hg
    simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7513 (p : Pattern) (guard : d1254 p = 1) : d653 p ≤ (0 : Int) + d334 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7512 p hg
    simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7514 (p : Pattern) (guard : d1254 p = 1) : d653 p ≤ (0 : Int) + d335 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7513 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7515 (p : Pattern) (guard : d1250 p = 1) : d656 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7516 (p : Pattern) (guard : d1240 p = 1) : d655 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7517 (p : Pattern) (guard : d1240 p = 1) : d656 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7498 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7516 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7518 (p : Pattern) (guard : d1253 p = 1) : d656 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7517 p hg
    simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7519 (p : Pattern) (guard : d1254 p = 1) : d656 p ≤ (0 : Int) + d336 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7518 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7520 (p : Pattern) (guard : d1240 p = 1) : d655 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d655, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d655, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d655, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d655, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7521 (p : Pattern) (guard : d1240 p = 1) : d656 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d656, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7504 p hg
    simpa only [d656, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d656, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7520 p hg
    simpa only [d656, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7522 (p : Pattern) (guard : d1253 p = 1) : d656 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7521 p hg
    simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7523 (p : Pattern) (guard : d1254 p = 1) : d656 p ≤ (0 : Int) + d338 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7522 p hg
    simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7524 (p : Pattern) (guard : d1254 p = 1) : d656 p ≤ (0 : Int) + d339 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7519 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7523 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7525 (p : Pattern) (guard : d1254 p = 1) : d657 p ≤ (0 : Int) + d340 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d657, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7514 p hg
    simpa only [d657, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d657, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7524 p hg
    simpa only [d657, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7526 (p : Pattern) (guard : d1254 p = 1) : d658 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d658, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d658, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d658, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7525 p hg
    simpa only [d658, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7527 (p : Pattern) (guard : d1240 p = 1) : d659 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d659, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d659, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d659, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d659, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7528 (p : Pattern) (guard : d1240 p = 1) : d660 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d660, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d660, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d660, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7527 p hg
    simpa only [d660, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7529 (p : Pattern) (guard : d1253 p = 1) : d660 p ≤ (0 : Int) + d342 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7528 p hg
    simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7530 (p : Pattern) (guard : d1254 p = 1) : d661 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d661, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d1254, d661, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d661, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7529 p hg
    simpa only [d1254, d661, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7531 (p : Pattern) (guard : d1254 p = 1) : d662 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d662, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d662, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d662, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7530 p hg
    simpa only [d662, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7532 (p : Pattern) (guard : d1253 p = 1) : d659 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7527 p hg
    simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7533 (p : Pattern) (guard : d1254 p = 1) : d663 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d663, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d1254, d663, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d663, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d1254, d663, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7534 (p : Pattern) (guard : d1254 p = 1) : d664 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d664, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d664, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d664, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7533 p hg
    simpa only [d664, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7535 (p : Pattern) (guard : d1254 p = 1) : d665 p ≤ (0 : Int) + d348 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d665, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7531 p hg
    simpa only [d665, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d665, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d665, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7536 (p : Pattern) (guard : d1254 p = 1) : d666 p ≤ (0 : Int) + d349 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d666, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d1254, d666, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d666, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d1254, d666, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7537 (p : Pattern) (guard : d1254 p = 1) : d667 p ≤ (0 : Int) + d350 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d667, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d667, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d667, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7536 p hg
    simpa only [d667, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7538 (p : Pattern) (guard : d1254 p = 1) : d668 p ≤ (0 : Int) + d351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d668, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d1254, d668, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d668, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d1254, d668, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7539 (p : Pattern) (guard : d1254 p = 1) : d669 p ≤ (0 : Int) + d352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d669, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7519 p hg
    simpa only [d669, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d669, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7538 p hg
    simpa only [d669, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7540 (p : Pattern) (guard : d1254 p = 1) : d670 p ≤ (0 : Int) + d353 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d670, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7537 p hg
    simpa only [d670, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d670, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7539 p hg
    simpa only [d670, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7541 (p : Pattern) (guard : d1254 p = 1) : d671 p ≤ (0 : Int) + d354 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d671, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7535 p hg
    simpa only [d671, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d671, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7540 p hg
    simpa only [d671, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7542 (p : Pattern) (guard : d1254 p = 1) : d672 p ≤ (0 : Int) + d355 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d672, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d672, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d672, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7541 p hg
    simpa only [d672, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7543 (p : Pattern) (guard : d1250 p = 1) : d673 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7544 (p : Pattern) (guard : d1240 p = 1) : d673 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7516 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7545 (p : Pattern) (guard : d1253 p = 1) : d673 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7544 p hg
    simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7546 (p : Pattern) (guard : d1254 p = 1) : d673 p ≤ (0 : Int) + d356 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7543 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7545 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7547 (p : Pattern) (guard : d1240 p = 1) : d673 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d673, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d673, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d673, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7520 p hg
    simpa only [d673, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7548 (p : Pattern) (guard : d1253 p = 1) : d673 p ≤ (0 : Int) + d357 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7547 p hg
    simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7549 (p : Pattern) (guard : d1254 p = 1) : d673 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7543 p hg
    simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7548 p hg
    simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7550 (p : Pattern) (guard : d1254 p = 1) : d673 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7546 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7549 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7551 (p : Pattern) (guard : d1254 p = 1) : d674 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7550 p hg
    simpa only [d674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7552 (p : Pattern) (guard : d1250 p = 1) : d660 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7553 (p : Pattern) (guard : d1240 p = 1) : d659 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7554 (p : Pattern) (guard : d1240 p = 1) : d660 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7553 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7555 (p : Pattern) (guard : d1253 p = 1) : d660 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7554 p hg
    simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7556 (p : Pattern) (guard : d1254 p = 1) : d660 p ≤ (0 : Int) + d361 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7552 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7555 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7557 (p : Pattern) (guard : d1254 p = 1) : d660 p ≤ (0 : Int) + d362 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7552 p hg
    simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7529 p hg
    simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7558 (p : Pattern) (guard : d1254 p = 1) : d660 p ≤ (0 : Int) + d363 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7556 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7557 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7559 (p : Pattern) (guard : d1254 p = 1) : d675 p ≤ (0 : Int) + d364 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d675, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7551 p hg
    simpa only [d675, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d675, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7558 p hg
    simpa only [d675, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
