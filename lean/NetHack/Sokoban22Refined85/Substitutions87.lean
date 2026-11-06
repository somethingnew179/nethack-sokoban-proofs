/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions86
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10440 (p : Pattern) : d1699 (change p 204 (some 182)) = d5856 p := by
  change (if p 163 then d1698 (change p 204 (some 182)) else d1692 (change p 204 (some 182))) = d5856 p
  rw [sub10439, sub10428]
  rfl
theorem sub10441 (p : Pattern) : d1700 (change p 204 (some 182)) = d5857 p := by
  change (if p 162 then d1699 (change p 204 (some 182)) else d1691 (change p 204 (some 182))) = d5857 p
  rw [sub10440, sub10427]
  rfl
theorem sub10442 (p : Pattern) : d9 (change p 204 (some 182)) = d9 p := by
  rfl
theorem sub10443 (p : Pattern) : d23 (change p 204 (some 182)) = d23 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d9 (change p 204 (some 182))) = d23 p
  rw [sub10415, sub10442]
  rfl
theorem sub10444 (p : Pattern) : d24 (change p 204 (some 182)) = d24 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d9 (change p 204 (some 182))) = d24 p
  rw [sub10443, sub10442]
  rfl
theorem sub10445 (p : Pattern) : d11 (change p 204 (some 182)) = d11 p := by
  rfl
theorem sub10446 (p : Pattern) : d1701 (change p 204 (some 182)) = d1701 p := by
  change (if p 247 then d11 (change p 204 (some 182)) else d9 (change p 204 (some 182))) = d1701 p
  rw [sub10445, sub10442]
  rfl
theorem sub10447 (p : Pattern) : d39 (change p 204 (some 182)) = d39 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d11 (change p 204 (some 182))) = d39 p
  rw [sub10415, sub10445]
  rfl
theorem sub10448 (p : Pattern) : d1702 (change p 204 (some 182)) = d1702 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d1701 (change p 204 (some 182))) = d1702 p
  rw [sub10447, sub10446]
  rfl
theorem sub10449 (p : Pattern) : d1703 (change p 204 (some 182)) = d1703 p := by
  change (if p 225 then d1702 (change p 204 (some 182)) else d24 (change p 204 (some 182))) = d1703 p
  rw [sub10448, sub10444]
  rfl
theorem sub10450 (p : Pattern) : d1704 (change p 204 (some 182)) = d1704 p := by
  change (if p 224 then d1702 (change p 204 (some 182)) else d1703 (change p 204 (some 182))) = d1704 p
  rw [sub10448, sub10449]
  rfl
theorem sub10451 (p : Pattern) : d1705 (change p 204 (some 182)) = d1704 p := by
  change d1704 (change p 204 (some 182)) = d1704 p
  exact sub10450 p
theorem sub10452 (p : Pattern) : d1706 (change p 204 (some 182)) = d1704 p := by
  change d1705 (change p 204 (some 182)) = d1704 p
  exact sub10451 p
theorem sub10453 (p : Pattern) : d1707 (change p 204 (some 182)) = d5858 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1706 (change p 204 (some 182))) = d5858 p
  rw [sub10415, sub10452]
  rfl
theorem sub10454 (p : Pattern) : d1708 (change p 204 (some 182)) = d5859 p := by
  change (if p 162 then d1707 (change p 204 (some 182)) else d1699 (change p 204 (some 182))) = d5859 p
  rw [sub10453, sub10440]
  rfl
theorem sub10455 (p : Pattern) : d1709 (change p 204 (some 182)) = d5860 p := by
  change (if p 161 then d1708 (change p 204 (some 182)) else d1700 (change p 204 (some 182))) = d5860 p
  rw [sub10454, sub10441]
  rfl
theorem sub10456 (p : Pattern) : d31 (change p 204 (some 182)) = d31 p := by
  change (if p 246 then d30 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d31 p
  rw [sub10420, sub10418]
  rfl
theorem sub10457 (p : Pattern) : d8 (change p 204 (some 182)) = d8 p := by
  rfl
theorem sub10458 (p : Pattern) : d1710 (change p 204 (some 182)) = d1710 p := by
  change (if p 247 then d8 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d1710 p
  rw [sub10457, sub10418]
  rfl
theorem sub10459 (p : Pattern) : d190 (change p 204 (some 182)) = d190 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d8 (change p 204 (some 182))) = d190 p
  rw [sub10415, sub10457]
  rfl
theorem sub10460 (p : Pattern) : d1711 (change p 204 (some 182)) = d1711 p := by
  change (if p 246 then d190 (change p 204 (some 182)) else d1710 (change p 204 (some 182))) = d1711 p
  rw [sub10459, sub10458]
  rfl
theorem sub10461 (p : Pattern) : d1712 (change p 204 (some 182)) = d1712 p := by
  change (if p 225 then d1711 (change p 204 (some 182)) else d31 (change p 204 (some 182))) = d1712 p
  rw [sub10460, sub10456]
  rfl
theorem sub10462 (p : Pattern) : d1713 (change p 204 (some 182)) = d1713 p := by
  change (if p 247 then d6 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d1713 p
  rw [sub10432, sub10418]
  rfl
theorem sub10463 (p : Pattern) : d1714 (change p 204 (some 182)) = d1714 p := by
  change (if p 246 then d34 (change p 204 (some 182)) else d1713 (change p 204 (some 182))) = d1714 p
  rw [sub10434, sub10462]
  rfl
theorem sub10464 (p : Pattern) : d1715 (change p 204 (some 182)) = d1715 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d30 (change p 204 (some 182))) = d1715 p
  rw [sub10447, sub10420]
  rfl
theorem sub10465 (p : Pattern) : d1716 (change p 204 (some 182)) = d1716 p := by
  change (if p 225 then d1715 (change p 204 (some 182)) else d1714 (change p 204 (some 182))) = d1716 p
  rw [sub10464, sub10463]
  rfl
theorem sub10466 (p : Pattern) : d1717 (change p 204 (some 182)) = d1717 p := by
  change (if p 224 then d1716 (change p 204 (some 182)) else d1712 (change p 204 (some 182))) = d1717 p
  rw [sub10465, sub10461]
  rfl
theorem sub10467 (p : Pattern) : d1718 (change p 204 (some 182)) = d1717 p := by
  change d1717 (change p 204 (some 182)) = d1717 p
  exact sub10466 p
theorem sub10468 (p : Pattern) : d1719 (change p 204 (some 182)) = d1717 p := by
  change d1718 (change p 204 (some 182)) = d1717 p
  exact sub10467 p
theorem sub10469 (p : Pattern) : d35 (change p 204 (some 182)) = d35 p := by
  change (if p 246 then d34 (change p 204 (some 182)) else d6 (change p 204 (some 182))) = d35 p
  rw [sub10434, sub10432]
  rfl
theorem sub10470 (p : Pattern) : d364 (change p 204 (some 182)) = d364 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d34 (change p 204 (some 182))) = d364 p
  rw [sub10415, sub10434]
  rfl
theorem sub10471 (p : Pattern) : d1720 (change p 204 (some 182)) = d1720 p := by
  change (if p 225 then d364 (change p 204 (some 182)) else d35 (change p 204 (some 182))) = d1720 p
  rw [sub10470, sub10469]
  rfl
theorem sub10472 (p : Pattern) : d10 (change p 204 (some 182)) = d10 p := by
  rfl
theorem sub10473 (p : Pattern) : d1721 (change p 204 (some 182)) = d1721 p := by
  change (if p 247 then d10 (change p 204 (some 182)) else d6 (change p 204 (some 182))) = d1721 p
  rw [sub10472, sub10432]
  rfl
theorem sub10474 (p : Pattern) : d57 (change p 204 (some 182)) = d57 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d10 (change p 204 (some 182))) = d57 p
  rw [sub10415, sub10472]
  rfl
theorem sub10475 (p : Pattern) : d1722 (change p 204 (some 182)) = d1722 p := by
  change (if p 246 then d57 (change p 204 (some 182)) else d1721 (change p 204 (some 182))) = d1722 p
  rw [sub10474, sub10473]
  rfl
theorem sub10476 (p : Pattern) : d1723 (change p 204 (some 182)) = d1723 p := by
  change (if p 225 then d364 (change p 204 (some 182)) else d1722 (change p 204 (some 182))) = d1723 p
  rw [sub10470, sub10475]
  rfl
theorem sub10477 (p : Pattern) : d1724 (change p 204 (some 182)) = d1724 p := by
  change (if p 224 then d1723 (change p 204 (some 182)) else d1720 (change p 204 (some 182))) = d1724 p
  rw [sub10476, sub10471]
  rfl
theorem sub10478 (p : Pattern) : d1725 (change p 204 (some 182)) = d1724 p := by
  change d1724 (change p 204 (some 182)) = d1724 p
  exact sub10477 p
theorem sub10479 (p : Pattern) : d1726 (change p 204 (some 182)) = d1724 p := by
  change d1725 (change p 204 (some 182)) = d1724 p
  exact sub10478 p
theorem sub10480 (p : Pattern) : d1727 (change p 204 (some 182)) = d5861 p := by
  change (if p 163 then d1726 (change p 204 (some 182)) else d1719 (change p 204 (some 182))) = d5861 p
  rw [sub10479, sub10468]
  rfl
theorem sub10481 (p : Pattern) : d40 (change p 204 (some 182)) = d40 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d11 (change p 204 (some 182))) = d40 p
  rw [sub10447, sub10445]
  rfl
theorem sub10482 (p : Pattern) : d327 (change p 204 (some 182)) = d327 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d39 (change p 204 (some 182))) = d327 p
  rw [sub10415, sub10447]
  rfl
theorem sub10483 (p : Pattern) : d1728 (change p 204 (some 182)) = d1728 p := by
  change (if p 225 then d327 (change p 204 (some 182)) else d40 (change p 204 (some 182))) = d1728 p
  rw [sub10482, sub10481]
  rfl
theorem sub10484 (p : Pattern) : d1729 (change p 204 (some 182)) = d1729 p := by
  change (if p 224 then d327 (change p 204 (some 182)) else d1728 (change p 204 (some 182))) = d1729 p
  rw [sub10482, sub10483]
  rfl
theorem sub10485 (p : Pattern) : d1730 (change p 204 (some 182)) = d1729 p := by
  change d1729 (change p 204 (some 182)) = d1729 p
  exact sub10484 p
theorem sub10486 (p : Pattern) : d1731 (change p 204 (some 182)) = d1729 p := by
  change d1730 (change p 204 (some 182)) = d1729 p
  exact sub10485 p
theorem sub10487 (p : Pattern) : d1732 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10488 (p : Pattern) : d1733 (change p 204 (some 182)) = d5862 p := by
  change (if p 163 then d1732 (change p 204 (some 182)) else d1731 (change p 204 (some 182))) = d5862 p
  rw [sub10487, sub10486]
  rfl
theorem sub10489 (p : Pattern) : d1734 (change p 204 (some 182)) = d5863 p := by
  change (if p 162 then d1733 (change p 204 (some 182)) else d1727 (change p 204 (some 182))) = d5863 p
  rw [sub10488, sub10480]
  rfl
theorem sub10490 (p : Pattern) : d1735 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10491 (p : Pattern) : d1736 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d1732 (change p 204 (some 182)) else d1735 (change p 204 (some 182))) = d12 p
  rw [sub10487, sub10490]
  simp only [ite_self]
theorem sub10492 (p : Pattern) : d527 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10493 (p : Pattern) : d528 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d527 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10492]
  simp only [ite_self]
theorem sub10494 (p : Pattern) : d1737 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d528 (change p 204 (some 182)) else d1736 (change p 204 (some 182))) = d12 p
  rw [sub10493, sub10491]
  simp only [ite_self]
theorem sub10495 (p : Pattern) : d1738 (change p 204 (some 182)) = d5864 p := by
  change (if p 161 then d1737 (change p 204 (some 182)) else d1734 (change p 204 (some 182))) = d5864 p
  rw [sub10494, sub10489]
  rfl
theorem sub10496 (p : Pattern) : d1739 (change p 204 (some 182)) = d5865 p := by
  change (if p 160 then d1738 (change p 204 (some 182)) else d1709 (change p 204 (some 182))) = d5865 p
  rw [sub10495, sub10455]
  rfl
theorem sub10497 (p : Pattern) : d1741 (change p 204 (some 182)) = d1686 p := by
  change d1687 (change p 204 (some 182)) = d1686 p
  exact sub10424 p
theorem sub10498 (p : Pattern) : d1742 (change p 204 (some 182)) = d1742 p := by
  change (if p 247 then d4 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d1742 p
  rw [sub10429, sub10418]
  rfl
theorem sub10499 (p : Pattern) : d1743 (change p 204 (some 182)) = d1743 p := by
  change (if p 246 then d17 (change p 204 (some 182)) else d1742 (change p 204 (some 182))) = d1743 p
  rw [sub10430, sub10498]
  rfl
theorem sub10500 (p : Pattern) : d1744 (change p 204 (some 182)) = d1744 p := by
  change (if p 225 then d1743 (change p 204 (some 182)) else d31 (change p 204 (some 182))) = d1744 p
  rw [sub10499, sub10456]
  rfl
theorem sub10501 (p : Pattern) : d1745 (change p 204 (some 182)) = d1745 p := by
  change (if p 224 then d1743 (change p 204 (some 182)) else d1744 (change p 204 (some 182))) = d1745 p
  rw [sub10499, sub10500]
  rfl
theorem sub10502 (p : Pattern) : d1746 (change p 204 (some 182)) = d1745 p := by
  change d1745 (change p 204 (some 182)) = d1745 p
  exact sub10501 p
theorem sub10503 (p : Pattern) : d1747 (change p 204 (some 182)) = d1745 p := by
  change d1746 (change p 204 (some 182)) = d1745 p
  exact sub10502 p
theorem sub10504 (p : Pattern) : d1748 (change p 204 (some 182)) = d5866 p := by
  change (if p 163 then d1747 (change p 204 (some 182)) else d1741 (change p 204 (some 182))) = d5866 p
  rw [sub10503, sub10497]
  rfl
theorem sub10505 (p : Pattern) : d1749 (change p 204 (some 182)) = d5867 p := by
  change (if p 163 then d1706 (change p 204 (some 182)) else d1698 (change p 204 (some 182))) = d5867 p
  rw [sub10452, sub10439]
  rfl
theorem sub10506 (p : Pattern) : d1750 (change p 204 (some 182)) = d5868 p := by
  change (if p 162 then d1749 (change p 204 (some 182)) else d1748 (change p 204 (some 182))) = d5868 p
  rw [sub10505, sub10504]
  rfl
theorem sub10507 (p : Pattern) : d58 (change p 204 (some 182)) = d58 p := by
  change (if p 246 then d57 (change p 204 (some 182)) else d10 (change p 204 (some 182))) = d58 p
  rw [sub10474, sub10472]
  rfl
theorem sub10508 (p : Pattern) : d329 (change p 204 (some 182)) = d329 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d57 (change p 204 (some 182))) = d329 p
  rw [sub10415, sub10474]
  rfl
theorem sub10509 (p : Pattern) : d1751 (change p 204 (some 182)) = d1751 p := by
  change (if p 225 then d329 (change p 204 (some 182)) else d58 (change p 204 (some 182))) = d1751 p
  rw [sub10508, sub10507]
  rfl
theorem sub10510 (p : Pattern) : d1752 (change p 204 (some 182)) = d1752 p := by
  change (if p 224 then d329 (change p 204 (some 182)) else d1751 (change p 204 (some 182))) = d1752 p
  rw [sub10508, sub10509]
  rfl
theorem sub10511 (p : Pattern) : d1753 (change p 204 (some 182)) = d1752 p := by
  change d1752 (change p 204 (some 182)) = d1752 p
  exact sub10510 p
theorem sub10512 (p : Pattern) : d1754 (change p 204 (some 182)) = d1752 p := by
  change d1753 (change p 204 (some 182)) = d1752 p
  exact sub10511 p
theorem sub10513 (p : Pattern) : d1755 (change p 204 (some 182)) = d5869 p := by
  change (if p 163 then d1754 (change p 204 (some 182)) else d1698 (change p 204 (some 182))) = d5869 p
  rw [sub10512, sub10439]
  rfl
theorem sub10514 (p : Pattern) : d1756 (change p 204 (some 182)) = d1729 p := by
  change d1730 (change p 204 (some 182)) = d1729 p
  exact sub10485 p
theorem sub10515 (p : Pattern) : d1757 (change p 204 (some 182)) = d5862 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1756 (change p 204 (some 182))) = d5862 p
  rw [sub10415, sub10514]
  rfl
theorem sub10516 (p : Pattern) : d1758 (change p 204 (some 182)) = d5870 p := by
  change (if p 162 then d1757 (change p 204 (some 182)) else d1755 (change p 204 (some 182))) = d5870 p
  rw [sub10515, sub10513]
  rfl
theorem sub10517 (p : Pattern) : d1759 (change p 204 (some 182)) = d5871 p := by
  change (if p 161 then d1758 (change p 204 (some 182)) else d1750 (change p 204 (some 182))) = d5871 p
  rw [sub10516, sub10506]
  rfl
theorem sub10518 (p : Pattern) : d1760 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10519 (p : Pattern) : d1761 (change p 204 (some 182)) = d5872 p := by
  change (if p 163 then d1760 (change p 204 (some 182)) else d1726 (change p 204 (some 182))) = d5872 p
  rw [sub10518, sub10479]
  rfl
theorem sub10520 (p : Pattern) : d1762 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d527 (change p 204 (some 182)) else d1732 (change p 204 (some 182))) = d12 p
  rw [sub10492, sub10487]
  simp only [ite_self]
theorem sub10521 (p : Pattern) : d1763 (change p 204 (some 182)) = d5873 p := by
  change (if p 162 then d1762 (change p 204 (some 182)) else d1761 (change p 204 (some 182))) = d5873 p
  rw [sub10520, sub10519]
  rfl
theorem sub10522 (p : Pattern) : d277 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10523 (p : Pattern) : d1764 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d277 (change p 204 (some 182)) else d1732 (change p 204 (some 182))) = d12 p
  rw [sub10522, sub10487]
  simp only [ite_self]
theorem sub10524 (p : Pattern) : d538 (change p 204 (some 182)) = d12 p := by
  change d12 (change p 204 (some 182)) = d12 p
  exact sub10415 p
theorem sub10525 (p : Pattern) : d539 (change p 204 (some 182)) = d12 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d538 (change p 204 (some 182))) = d12 p
  rw [sub10415, sub10524]
  simp only [ite_self]
theorem sub10526 (p : Pattern) : d1765 (change p 204 (some 182)) = d12 p := by
  change (if p 162 then d539 (change p 204 (some 182)) else d1764 (change p 204 (some 182))) = d12 p
  rw [sub10525, sub10523]
  simp only [ite_self]
theorem sub10527 (p : Pattern) : d1766 (change p 204 (some 182)) = d5874 p := by
  change (if p 161 then d1765 (change p 204 (some 182)) else d1763 (change p 204 (some 182))) = d5874 p
  rw [sub10526, sub10521]
  rfl
theorem sub10528 (p : Pattern) : d1767 (change p 204 (some 182)) = d5875 p := by
  change (if p 160 then d1766 (change p 204 (some 182)) else d1759 (change p 204 (some 182))) = d5875 p
  rw [sub10527, sub10517]
  rfl
theorem sub10529 (p : Pattern) : d1768 (change p 204 (some 182)) = d5876 p := by
  change (if p 141 then d1767 (change p 204 (some 182)) else d1739 (change p 204 (some 182))) = d5876 p
  rw [sub10528, sub10496]
  rfl
theorem sub10530 (p : Pattern) : d1769 (change p 204 (some 182)) = d1769 p := by
  change (if p 247 then d4 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d1769 p
  rw [sub10429, sub10414]
  rfl
theorem sub10531 (p : Pattern) : d1770 (change p 204 (some 182)) = d1770 p := by
  change (if p 246 then d17 (change p 204 (some 182)) else d1769 (change p 204 (some 182))) = d1770 p
  rw [sub10430, sub10530]
  rfl
theorem sub10532 (p : Pattern) : d1771 (change p 204 (some 182)) = d1771 p := by
  change (if p 225 then d1770 (change p 204 (some 182)) else d14 (change p 204 (some 182))) = d1771 p
  rw [sub10531, sub10417]
  rfl
theorem sub10533 (p : Pattern) : d1772 (change p 204 (some 182)) = d1772 p := by
  change (if p 224 then d1770 (change p 204 (some 182)) else d1771 (change p 204 (some 182))) = d1772 p
  rw [sub10531, sub10532]
  rfl
theorem sub10534 (p : Pattern) : d1773 (change p 204 (some 182)) = d1772 p := by
  change d1772 (change p 204 (some 182)) = d1772 p
  exact sub10533 p
theorem sub10535 (p : Pattern) : d1774 (change p 204 (some 182)) = d1772 p := by
  change d1773 (change p 204 (some 182)) = d1772 p
  exact sub10534 p
theorem sub10536 (p : Pattern) : d1775 (change p 204 (some 182)) = d1775 p := by
  change (if p 247 then d6 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d1775 p
  rw [sub10432, sub10414]
  rfl
theorem sub10537 (p : Pattern) : d1776 (change p 204 (some 182)) = d1776 p := by
  change (if p 246 then d34 (change p 204 (some 182)) else d1775 (change p 204 (some 182))) = d1776 p
  rw [sub10434, sub10536]
  rfl
theorem sub10538 (p : Pattern) : d1777 (change p 204 (some 182)) = d1777 p := by
  change (if p 225 then d1776 (change p 204 (some 182)) else d14 (change p 204 (some 182))) = d1777 p
  rw [sub10537, sub10417]
  rfl
theorem sub10539 (p : Pattern) : d1778 (change p 204 (some 182)) = d1778 p := by
  change (if p 247 then d8 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d1778 p
  rw [sub10457, sub10414]
  rfl
theorem sub10540 (p : Pattern) : d1779 (change p 204 (some 182)) = d1779 p := by
  change (if p 246 then d190 (change p 204 (some 182)) else d1778 (change p 204 (some 182))) = d1779 p
  rw [sub10459, sub10539]
  rfl
theorem sub10541 (p : Pattern) : d1780 (change p 204 (some 182)) = d1780 p := by
  change (if p 225 then d1779 (change p 204 (some 182)) else d1770 (change p 204 (some 182))) = d1780 p
  rw [sub10540, sub10531]
  rfl
theorem sub10542 (p : Pattern) : d1781 (change p 204 (some 182)) = d1781 p := by
  change (if p 224 then d1780 (change p 204 (some 182)) else d1777 (change p 204 (some 182))) = d1781 p
  rw [sub10541, sub10538]
  rfl
theorem sub10543 (p : Pattern) : d1782 (change p 204 (some 182)) = d1781 p := by
  change d1781 (change p 204 (some 182)) = d1781 p
  exact sub10542 p
theorem sub10544 (p : Pattern) : d1783 (change p 204 (some 182)) = d1781 p := by
  change d1782 (change p 204 (some 182)) = d1781 p
  exact sub10543 p
theorem sub10545 (p : Pattern) : d1784 (change p 204 (some 182)) = d5877 p := by
  change (if p 163 then d1783 (change p 204 (some 182)) else d1774 (change p 204 (some 182))) = d5877 p
  rw [sub10544, sub10535]
  rfl
theorem sub10546 (p : Pattern) : d1785 (change p 204 (some 182)) = d1785 p := by
  change (if p 247 then d11 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d1785 p
  rw [sub10445, sub10414]
  rfl
theorem sub10547 (p : Pattern) : d1786 (change p 204 (some 182)) = d1786 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d1785 (change p 204 (some 182))) = d1786 p
  rw [sub10443, sub10546]
  rfl
theorem sub10548 (p : Pattern) : d1787 (change p 204 (some 182)) = d1787 p := by
  change (if p 225 then d1786 (change p 204 (some 182)) else d1770 (change p 204 (some 182))) = d1787 p
  rw [sub10547, sub10531]
  rfl
theorem sub10549 (p : Pattern) : d1788 (change p 204 (some 182)) = d1788 p := by
  change (if p 224 then d1787 (change p 204 (some 182)) else d1777 (change p 204 (some 182))) = d1788 p
  rw [sub10548, sub10538]
  rfl
theorem sub10550 (p : Pattern) : d1789 (change p 204 (some 182)) = d1788 p := by
  change d1788 (change p 204 (some 182)) = d1788 p
  exact sub10549 p
theorem sub10551 (p : Pattern) : d1790 (change p 204 (some 182)) = d1788 p := by
  change d1789 (change p 204 (some 182)) = d1788 p
  exact sub10550 p
theorem sub10552 (p : Pattern) : d1791 (change p 204 (some 182)) = d1791 p := by
  change (if p 247 then d10 (change p 204 (some 182)) else d4 (change p 204 (some 182))) = d1791 p
  rw [sub10472, sub10429]
  rfl
theorem sub10553 (p : Pattern) : d1792 (change p 204 (some 182)) = d1792 p := by
  change (if p 246 then d57 (change p 204 (some 182)) else d1791 (change p 204 (some 182))) = d1792 p
  rw [sub10474, sub10552]
  rfl
theorem sub10554 (p : Pattern) : d1793 (change p 204 (some 182)) = d1793 p := by
  change (if p 225 then d1792 (change p 204 (some 182)) else d18 (change p 204 (some 182))) = d1793 p
  rw [sub10553, sub10431]
  rfl
theorem sub10555 (p : Pattern) : d1794 (change p 204 (some 182)) = d1794 p := by
  change (if p 247 then d8 (change p 204 (some 182)) else d4 (change p 204 (some 182))) = d1794 p
  rw [sub10457, sub10429]
  rfl
theorem sub10556 (p : Pattern) : d1795 (change p 204 (some 182)) = d1795 p := by
  change (if p 246 then d190 (change p 204 (some 182)) else d1794 (change p 204 (some 182))) = d1795 p
  rw [sub10459, sub10555]
  rfl
theorem sub10557 (p : Pattern) : d339 (change p 204 (some 182)) = d339 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d17 (change p 204 (some 182))) = d339 p
  rw [sub10415, sub10430]
  rfl
theorem sub10558 (p : Pattern) : d1796 (change p 204 (some 182)) = d1796 p := by
  change (if p 225 then d339 (change p 204 (some 182)) else d1795 (change p 204 (some 182))) = d1796 p
  rw [sub10557, sub10556]
  rfl
theorem sub10559 (p : Pattern) : d1797 (change p 204 (some 182)) = d1797 p := by
  change (if p 224 then d1796 (change p 204 (some 182)) else d1793 (change p 204 (some 182))) = d1797 p
  rw [sub10558, sub10554]
  rfl
end NetHack.Sokoban22Refined85
