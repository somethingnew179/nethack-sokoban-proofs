/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions37
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5700 (pattern : Twelve) : d1623 (change pattern 1 12) = d1623 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1617 (change pattern 1 12)) = d1623 pattern
  rw [s5467, s5699]
  rfl
theorem s5701 (pattern : Twelve) : d1627 (change pattern 1 12) = d1627 pattern := by
  change (if pattern.e then d1623 (change pattern 1 12) else d1622 (change pattern 1 12)) = d1627 pattern
  rw [s5700, s5698]
  rfl
theorem s5702 (pattern : Twelve) : d1630 (change pattern 1 12) = d1630 pattern := by
  change (if pattern.j then d1312 (change pattern 1 12) else d1627 (change pattern 1 12)) = d1630 pattern
  rw [s5657, s5701]
  rfl
theorem s5703 (pattern : Twelve) : d1618 (change pattern 1 12) = d1618 pattern := by
  change (if pattern.i then d118 (change pattern 1 12) else d119 (change pattern 1 12)) = d1618 pattern
  rw [s5575, s5564]
  rfl
theorem s5704 (pattern : Twelve) : d1620 (change pattern 1 12) = d1620 pattern := by
  change (if pattern.h then d1618 (change pattern 1 12) else d1282 (change pattern 1 12)) = d1620 pattern
  rw [s5703, s5635]
  rfl
theorem s5705 (pattern : Twelve) : d1624 (change pattern 1 12) = d1624 pattern := by
  change (if pattern.f then d1620 (change pattern 1 12) else d41 (change pattern 1 12)) = d1624 pattern
  rw [s5704, s5496]
  rfl
theorem s5706 (pattern : Twelve) : d1628 (change pattern 1 12) = d1628 pattern := by
  change (if pattern.e then d1304 (change pattern 1 12) else d1624 (change pattern 1 12)) = d1628 pattern
  rw [s5656, s5705]
  rfl
theorem s5707 (pattern : Twelve) : d182 (change pattern 1 12) = d182 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d118 (change pattern 1 12)) = d182 pattern
  rw [s5467, s5575]
  rfl
theorem s5708 (pattern : Twelve) : d1621 (change pattern 1 12) = d1621 pattern := by
  change (if pattern.h then d182 (change pattern 1 12) else d1331 (change pattern 1 12)) = d1621 pattern
  rw [s5707, s5684]
  rfl
theorem s5709 (pattern : Twelve) : d1625 (change pattern 1 12) = d1625 pattern := by
  change (if pattern.f then d1621 (change pattern 1 12) else d49 (change pattern 1 12)) = d1625 pattern
  rw [s5708, s5598]
  rfl
theorem s5710 (pattern : Twelve) : d1626 (change pattern 1 12) = d1626 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d1252 (change pattern 1 12)) = d1626 pattern
  rw [s5467, s5603]
  rfl
theorem s5711 (pattern : Twelve) : d1629 (change pattern 1 12) = d1629 pattern := by
  change (if pattern.e then d1626 (change pattern 1 12) else d1625 (change pattern 1 12)) = d1629 pattern
  rw [s5710, s5709]
  rfl
theorem s5712 (pattern : Twelve) : d1631 (change pattern 1 12) = d1631 pattern := by
  change (if pattern.j then d1629 (change pattern 1 12) else d1628 (change pattern 1 12)) = d1631 pattern
  rw [s5711, s5706]
  rfl
theorem s5713 (pattern : Twelve) : d1632 (change pattern 1 12) = d1632 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1312 (change pattern 1 12)) = d1632 pattern
  rw [s5467, s5657]
  rfl
theorem s5714 (pattern : Twelve) : d1633 (change pattern 1 12) = d1633 pattern := by
  change (if pattern.d then d1632 (change pattern 1 12) else d1631 (change pattern 1 12)) = d1633 pattern
  rw [s5713, s5712]
  rfl
theorem s5715 (pattern : Twelve) : d1634 (change pattern 1 12) = d1634 pattern := by
  change (if pattern.c then d1633 (change pattern 1 12) else d1630 (change pattern 1 12)) = d1634 pattern
  rw [s5714, s5702]
  rfl
theorem s5716 (pattern : Twelve) : d1635 (change pattern 1 12) = d1635 pattern := by
  change (if pattern.g then d1634 (change pattern 1 12) else d1353 (change pattern 1 12)) = d1635 pattern
  rw [s5715, s5695]
  rfl
theorem s5717 (pattern : Twelve) : d1641 (change pattern 1 12) = d1635 pattern := by
  change d1635 (change pattern 1 12) = d1635 pattern
  exact s5716 pattern
theorem s5718 (pattern : Twelve) : d1642 (change pattern 1 12) = d1636 pattern := by
  change (if pattern.a then d1641 (change pattern 1 12) else d1640 (change pattern 1 12)) = d1636 pattern
  rw [s5717, s5663]
  rfl
theorem s5719 (pattern : Twelve) : d1649 (change pattern 1 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 1 12) else d19 (change pattern 1 12)) = d1649 pattern
  rw [s5664, s5460]
  rfl
theorem s5720 (pattern : Twelve) : d1650 (change pattern 1 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d25 (change pattern 1 12)) = d1650 pattern
  rw [s5467, s5465]
  rfl
theorem s5721 (pattern : Twelve) : d1656 (change pattern 1 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 1 12) else d1649 (change pattern 1 12)) = d1656 pattern
  rw [s5720, s5719]
  rfl
theorem s5722 (pattern : Twelve) : d1644 (change pattern 1 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 1 12) else d1324 (change pattern 1 12)) = d1644 pattern
  rw [s5678, s5664]
  rfl
theorem s5723 (pattern : Twelve) : d1645 (change pattern 1 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d1324 (change pattern 1 12)) = d1645 pattern
  rw [s5467, s5664]
  rfl
theorem s5724 (pattern : Twelve) : d1647 (change pattern 1 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 1 12) else d1644 (change pattern 1 12)) = d1647 pattern
  rw [s5723, s5722]
  rfl
theorem s5725 (pattern : Twelve) : d1651 (change pattern 1 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 1 12) else d1286 (change pattern 1 12)) = d1651 pattern
  rw [s5724, s5625]
  rfl
theorem s5726 (pattern : Twelve) : d1657 (change pattern 1 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 1 12) else d1651 (change pattern 1 12)) = d1657 pattern
  rw [s5639, s5725]
  rfl
theorem s5727 (pattern : Twelve) : d1660 (change pattern 1 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 1 12) else d1656 (change pattern 1 12)) = d1660 pattern
  rw [s5726, s5721]
  rfl
theorem s5728 (pattern : Twelve) : d1652 (change pattern 1 12) = d1652 pattern := by
  change (if pattern.f then d1644 (change pattern 1 12) else d817 (change pattern 1 12)) = d1652 pattern
  rw [s5722, s5466]
  rfl
theorem s5729 (pattern : Twelve) : d1653 (change pattern 1 12) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d821 (change pattern 1 12)) = d1653 pattern
  rw [s5467, s5506]
  rfl
theorem s5730 (pattern : Twelve) : d1658 (change pattern 1 12) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 1 12) else d1652 (change pattern 1 12)) = d1658 pattern
  rw [s5729, s5728]
  rfl
theorem s5731 (pattern : Twelve) : d1646 (change pattern 1 12) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d20 (change pattern 1 12)) = d1646 pattern
  rw [s5569, s5678]
  rfl
theorem s5732 (pattern : Twelve) : d1648 (change pattern 1 12) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 1 12) else d1646 (change pattern 1 12)) = d1648 pattern
  rw [s5688, s5731]
  rfl
theorem s5733 (pattern : Twelve) : d1654 (change pattern 1 12) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 1 12) else d1289 (change pattern 1 12)) = d1654 pattern
  rw [s5732, s5638]
  rfl
theorem s5734 (pattern : Twelve) : d1655 (change pattern 1 12) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d822 (change pattern 1 12)) = d1655 pattern
  rw [s5467, s5507]
  rfl
theorem s5735 (pattern : Twelve) : d1659 (change pattern 1 12) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 1 12) else d1654 (change pattern 1 12)) = d1659 pattern
  rw [s5734, s5733]
  rfl
theorem s5736 (pattern : Twelve) : d1661 (change pattern 1 12) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 1 12) else d1658 (change pattern 1 12)) = d1661 pattern
  rw [s5735, s5730]
  rfl
theorem s5737 (pattern : Twelve) : d1662 (change pattern 1 12) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1657 (change pattern 1 12)) = d1662 pattern
  rw [s5467, s5726]
  rfl
theorem s5738 (pattern : Twelve) : d1663 (change pattern 1 12) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 1 12) else d1661 (change pattern 1 12)) = d1663 pattern
  rw [s5737, s5736]
  rfl
theorem s5739 (pattern : Twelve) : d1664 (change pattern 1 12) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 1 12) else d1660 (change pattern 1 12)) = d1664 pattern
  rw [s5738, s5727]
  rfl
theorem s5740 (pattern : Twelve) : d1831 (change pattern 1 12) = d1664 pattern := by
  change d1664 (change pattern 1 12) = d1664 pattern
  exact s5739 pattern
theorem s5741 (pattern : Twelve) : d1668 (change pattern 1 12) = d1668 pattern := by
  change (if pattern.f then d1644 (change pattern 1 12) else d19 (change pattern 1 12)) = d1668 pattern
  rw [s5722, s5460]
  rfl
theorem s5742 (pattern : Twelve) : d1671 (change pattern 1 12) = d1671 pattern := by
  change (if pattern.e then d1650 (change pattern 1 12) else d1668 (change pattern 1 12)) = d1671 pattern
  rw [s5720, s5741]
  rfl
theorem s5743 (pattern : Twelve) : d1674 (change pattern 1 12) = d1674 pattern := by
  change (if pattern.j then d1657 (change pattern 1 12) else d1671 (change pattern 1 12)) = d1674 pattern
  rw [s5726, s5742]
  rfl
theorem s5744 (pattern : Twelve) : d1665 (change pattern 1 12) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d1324 (change pattern 1 12)) = d1665 pattern
  rw [s5569, s5664]
  rfl
theorem s5745 (pattern : Twelve) : d1666 (change pattern 1 12) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 1 12) else d1644 (change pattern 1 12)) = d1666 pattern
  rw [s5744, s5722]
  rfl
theorem s5746 (pattern : Twelve) : d1669 (change pattern 1 12) = d1669 pattern := by
  change (if pattern.f then d1666 (change pattern 1 12) else d817 (change pattern 1 12)) = d1669 pattern
  rw [s5745, s5466]
  rfl
theorem s5747 (pattern : Twelve) : d1672 (change pattern 1 12) = d1672 pattern := by
  change (if pattern.e then d1300 (change pattern 1 12) else d1669 (change pattern 1 12)) = d1672 pattern
  rw [s5639, s5746]
  rfl
theorem s5748 (pattern : Twelve) : d183 (change pattern 1 12) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 1 12) else d22 (change pattern 1 12)) = d183 pattern
  rw [s5467, s5569]
  rfl
theorem s5749 (pattern : Twelve) : d1667 (change pattern 1 12) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 1 12) else d128 (change pattern 1 12)) = d1667 pattern
  rw [s5748, s5688]
  rfl
theorem s5750 (pattern : Twelve) : d1670 (change pattern 1 12) = d1670 pattern := by
  change (if pattern.f then d1667 (change pattern 1 12) else d1289 (change pattern 1 12)) = d1670 pattern
  rw [s5749, s5638]
  rfl
theorem s5751 (pattern : Twelve) : d1673 (change pattern 1 12) = d1673 pattern := by
  change (if pattern.e then d1626 (change pattern 1 12) else d1670 (change pattern 1 12)) = d1673 pattern
  rw [s5710, s5750]
  rfl
theorem s5752 (pattern : Twelve) : d1675 (change pattern 1 12) = d1675 pattern := by
  change (if pattern.j then d1673 (change pattern 1 12) else d1672 (change pattern 1 12)) = d1675 pattern
  rw [s5751, s5747]
  rfl
theorem s5753 (pattern : Twelve) : d1676 (change pattern 1 12) = d1676 pattern := by
  change (if pattern.d then d1662 (change pattern 1 12) else d1675 (change pattern 1 12)) = d1676 pattern
  rw [s5737, s5752]
  rfl
theorem s5754 (pattern : Twelve) : d1677 (change pattern 1 12) = d1677 pattern := by
  change (if pattern.c then d1676 (change pattern 1 12) else d1674 (change pattern 1 12)) = d1677 pattern
  rw [s5753, s5743]
  rfl
theorem s5755 (pattern : Twelve) : d1814 (change pattern 1 12) = d1814 pattern := by
  change (if pattern.f then d20 (change pattern 1 12) else d25 (change pattern 1 12)) = d1814 pattern
  rw [s5678, s5465]
  rfl
theorem s5756 (pattern : Twelve) : d1815 (change pattern 1 12) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 1 12) else d21 (change pattern 1 12)) = d1815 pattern
  rw [s5467, s5505]
  rfl
theorem s5757 (pattern : Twelve) : d1818 (change pattern 1 12) = d1818 pattern := by
  change (if pattern.e then d1815 (change pattern 1 12) else d1814 (change pattern 1 12)) = d1818 pattern
  rw [s5756, s5755]
  rfl
theorem s5758 (pattern : Twelve) : d1821 (change pattern 1 12) = d1821 pattern := by
  change (if pattern.j then d1659 (change pattern 1 12) else d1818 (change pattern 1 12)) = d1821 pattern
  rw [s5735, s5757]
  rfl
theorem s5759 (pattern : Twelve) : d1816 (change pattern 1 12) = d1816 pattern := by
  change (if pattern.f then d1646 (change pattern 1 12) else d821 (change pattern 1 12)) = d1816 pattern
  rw [s5731, s5506]
  rfl
theorem s5760 (pattern : Twelve) : d1819 (change pattern 1 12) = d1819 pattern := by
  change (if pattern.e then d1655 (change pattern 1 12) else d1816 (change pattern 1 12)) = d1819 pattern
  rw [s5734, s5759]
  rfl
theorem s5761 (pattern : Twelve) : d1817 (change pattern 1 12) = d1817 pattern := by
  change (if pattern.f then d183 (change pattern 1 12) else d822 (change pattern 1 12)) = d1817 pattern
  rw [s5748, s5507]
  rfl
theorem s5762 (pattern : Twelve) : d1820 (change pattern 1 12) = d1820 pattern := by
  change (if pattern.e then d6 (change pattern 1 12) else d1817 (change pattern 1 12)) = d1820 pattern
  rw [s5467, s5761]
  rfl
theorem s5763 (pattern : Twelve) : d1822 (change pattern 1 12) = d1822 pattern := by
  change (if pattern.j then d1820 (change pattern 1 12) else d1819 (change pattern 1 12)) = d1822 pattern
  rw [s5762, s5760]
  rfl
theorem s5764 (pattern : Twelve) : d1823 (change pattern 1 12) = d1823 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d1659 (change pattern 1 12)) = d1823 pattern
  rw [s5467, s5735]
  rfl
theorem s5765 (pattern : Twelve) : d1824 (change pattern 1 12) = d1824 pattern := by
  change (if pattern.d then d1823 (change pattern 1 12) else d1822 (change pattern 1 12)) = d1824 pattern
  rw [s5764, s5763]
  rfl
theorem s5766 (pattern : Twelve) : d1825 (change pattern 1 12) = d1825 pattern := by
  change (if pattern.c then d1824 (change pattern 1 12) else d1821 (change pattern 1 12)) = d1825 pattern
  rw [s5765, s5758]
  rfl
theorem s5767 (pattern : Twelve) : d1826 (change pattern 1 12) = d1826 pattern := by
  change (if pattern.g then d1825 (change pattern 1 12) else d1677 (change pattern 1 12)) = d1826 pattern
  rw [s5766, s5754]
  rfl
theorem s5768 (pattern : Twelve) : d1832 (change pattern 1 12) = d1826 pattern := by
  change d1826 (change pattern 1 12) = d1826 pattern
  exact s5767 pattern
theorem s5769 (pattern : Twelve) : d1833 (change pattern 1 12) = d1827 pattern := by
  change (if pattern.a then d1832 (change pattern 1 12) else d1831 (change pattern 1 12)) = d1827 pattern
  rw [s5768, s5740]
  rfl
theorem s5770 (pattern : Twelve) : d26 (change pattern 1 12) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 1 12) else d0 (change pattern 1 12)) = d26 pattern
  rw [s5448, s5447]
  rfl
theorem s5771 (pattern : Twelve) : d50 (change pattern 1 12) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 1 12) else d26 (change pattern 1 12)) = d50 pattern
  rw [s5451, s5770]
  rfl
theorem s5772 (pattern : Twelve) : d72 (change pattern 1 12) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 1 12) else d0 (change pattern 1 12)) = d72 pattern
  rw [s5771, s5447]
  rfl
theorem s5773 (pattern : Twelve) : d18 (change pattern 1 12) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 1 12) else d8 (change pattern 1 12)) = d18 pattern
  rw [s5475, s5544]
  rfl
theorem s5774 (pattern : Twelve) : d28 (change pattern 1 12) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 1 12) else d17 (change pattern 1 12)) = d28 pattern
  rw [s5773, s5450]
  rfl
theorem s5775 (pattern : Twelve) : d51 (change pattern 1 12) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 1 12) else d28 (change pattern 1 12)) = d51 pattern
  rw [s5624, s5774]
  rfl
theorem s5776 (pattern : Twelve) : d73 (change pattern 1 12) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 1 12) else d0 (change pattern 1 12)) = d73 pattern
  rw [s5775, s5447]
  rfl
theorem s5777 (pattern : Twelve) : d91 (change pattern 1 12) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 1 12) else d72 (change pattern 1 12)) = d91 pattern
  rw [s5776, s5772]
  rfl
theorem s5778 (pattern : Twelve) : d31 (change pattern 1 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 1 12) else d0 (change pattern 1 12)) = d31 pattern
  rw [s5678, s5447]
  rfl
theorem s5779 (pattern : Twelve) : d52 (change pattern 1 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 1 12) else d30 (change pattern 1 12)) = d52 pattern
  rw [s5778, s5472]
  rfl
theorem s5780 (pattern : Twelve) : d32 (change pattern 1 12) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 1 12) else d17 (change pattern 1 12)) = d32 pattern
  rw [s5505, s5450]
  rfl
theorem s5781 (pattern : Twelve) : d53 (change pattern 1 12) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 1 12) else d30 (change pattern 1 12)) = d53 pattern
  rw [s5780, s5472]
  rfl
theorem s5782 (pattern : Twelve) : d74 (change pattern 1 12) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 1 12) else d52 (change pattern 1 12)) = d74 pattern
  rw [s5781, s5779]
  rfl
theorem s5783 (pattern : Twelve) : d33 (change pattern 1 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d0 (change pattern 1 12)) = d33 pattern
  rw [s5569, s5447]
  rfl
theorem s5784 (pattern : Twelve) : d54 (change pattern 1 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 1 12) else d30 (change pattern 1 12)) = d54 pattern
  rw [s5783, s5472]
  rfl
theorem s5785 (pattern : Twelve) : d55 (change pattern 1 12) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 1 12) else d34 (change pattern 1 12)) = d55 pattern
  rw [s5624, s5477]
  rfl
theorem s5786 (pattern : Twelve) : d75 (change pattern 1 12) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 1 12) else d54 (change pattern 1 12)) = d75 pattern
  rw [s5785, s5784]
  rfl
theorem s5787 (pattern : Twelve) : d92 (change pattern 1 12) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 1 12) else d74 (change pattern 1 12)) = d92 pattern
  rw [s5786, s5782]
  rfl
theorem s5788 (pattern : Twelve) : d102 (change pattern 1 12) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 1 12) else d91 (change pattern 1 12)) = d102 pattern
  rw [s5787, s5777]
  rfl
theorem s5789 (pattern : Twelve) : d76 (change pattern 1 12) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 1 12) else d0 (change pattern 1 12)) = d76 pattern
  rw [s5785, s5447]
  rfl
theorem s5790 (pattern : Twelve) : d93 (change pattern 1 12) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 1 12) else d72 (change pattern 1 12)) = d93 pattern
  rw [s5789, s5772]
  rfl
theorem s5791 (pattern : Twelve) : d57 (change pattern 1 12) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 1 12) else d30 (change pattern 1 12)) = d57 pattern
  rw [s5481, s5472]
  rfl
theorem s5792 (pattern : Twelve) : d77 (change pattern 1 12) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 1 12) else d56 (change pattern 1 12)) = d77 pattern
  rw [s5791, s5474]
  rfl
theorem s5793 (pattern : Twelve) : d78 (change pattern 1 12) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 1 12) else d56 (change pattern 1 12)) = d78 pattern
  rw [s5785, s5474]
  rfl
theorem s5794 (pattern : Twelve) : d94 (change pattern 1 12) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 1 12) else d77 (change pattern 1 12)) = d94 pattern
  rw [s5793, s5792]
  rfl
theorem s5795 (pattern : Twelve) : d103 (change pattern 1 12) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 1 12) else d93 (change pattern 1 12)) = d103 pattern
  rw [s5794, s5790]
  rfl
theorem s5796 (pattern : Twelve) : d110 (change pattern 1 12) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 1 12) else d102 (change pattern 1 12)) = d110 pattern
  rw [s5795, s5788]
  rfl
theorem s5797 (pattern : Twelve) : d37 (change pattern 1 12) = d37 pattern := by
  change (if pattern.i then d3 (change pattern 1 12) else d17 (change pattern 1 12)) = d37 pattern
  rw [s5458, s5450]
  rfl
theorem s5798 (pattern : Twelve) : d58 (change pattern 1 12) = d58 pattern := by
  change (if pattern.h then d37 (change pattern 1 12) else d30 (change pattern 1 12)) = d58 pattern
  rw [s5797, s5472]
  rfl
theorem s5799 (pattern : Twelve) : d79 (change pattern 1 12) = d79 pattern := by
  change (if pattern.f then d58 (change pattern 1 12) else d30 (change pattern 1 12)) = d79 pattern
  rw [s5798, s5472]
  rfl
theorem s5800 (pattern : Twelve) : d80 (change pattern 1 12) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 1 12) else d30 (change pattern 1 12)) = d80 pattern
  rw [s5785, s5472]
  rfl
theorem s5801 (pattern : Twelve) : d95 (change pattern 1 12) = d95 pattern := by
  change (if pattern.e then d80 (change pattern 1 12) else d79 (change pattern 1 12)) = d95 pattern
  rw [s5800, s5799]
  rfl
theorem s5802 (pattern : Twelve) : d60 (change pattern 1 12) = d60 pattern := by
  change (if pattern.h then d40 (change pattern 1 12) else d38 (change pattern 1 12)) = d60 pattern
  rw [s5501, s5491]
  rfl
theorem s5803 (pattern : Twelve) : d81 (change pattern 1 12) = d81 pattern := by
  change (if pattern.f then d60 (change pattern 1 12) else d59 (change pattern 1 12)) = d81 pattern
  rw [s5802, s5493]
  rfl
theorem s5804 (pattern : Twelve) : d61 (change pattern 1 12) = d61 pattern := by
  change (if pattern.h then d42 (change pattern 1 12) else d41 (change pattern 1 12)) = d61 pattern
  rw [s5468, s5496]
  rfl
theorem s5805 (pattern : Twelve) : d82 (change pattern 1 12) = d82 pattern := by
  change (if pattern.f then d61 (change pattern 1 12) else d59 (change pattern 1 12)) = d82 pattern
  rw [s5804, s5493]
  rfl
theorem s5806 (pattern : Twelve) : d96 (change pattern 1 12) = d96 pattern := by
  change (if pattern.e then d82 (change pattern 1 12) else d81 (change pattern 1 12)) = d96 pattern
  rw [s5805, s5803]
  rfl
theorem s5807 (pattern : Twelve) : d104 (change pattern 1 12) = d104 pattern := by
  change (if pattern.j then d96 (change pattern 1 12) else d95 (change pattern 1 12)) = d104 pattern
  rw [s5806, s5801]
  rfl
theorem s5808 (pattern : Twelve) : d105 (change pattern 1 12) = d105 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d94 (change pattern 1 12)) = d105 pattern
  rw [s5467, s5794]
  rfl
theorem s5809 (pattern : Twelve) : d111 (change pattern 1 12) = d111 pattern := by
  change (if pattern.d then d105 (change pattern 1 12) else d104 (change pattern 1 12)) = d111 pattern
  rw [s5808, s5807]
  rfl
theorem s5810 (pattern : Twelve) : d114 (change pattern 1 12) = d114 pattern := by
  change (if pattern.c then d111 (change pattern 1 12) else d110 (change pattern 1 12)) = d114 pattern
  rw [s5809, s5796]
  rfl
theorem s5811 (pattern : Twelve) : d97 (change pattern 1 12) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 1 12) else d72 (change pattern 1 12)) = d97 pattern
  rw [s5800, s5772]
  rfl
theorem s5812 (pattern : Twelve) : d43 (change pattern 1 12) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 1 12) else d1 (change pattern 1 12)) = d43 pattern
  rw [s5505, s5448]
  rfl
theorem s5813 (pattern : Twelve) : d62 (change pattern 1 12) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 1 12) else d30 (change pattern 1 12)) = d62 pattern
  rw [s5812, s5472]
  rfl
theorem s5814 (pattern : Twelve) : d83 (change pattern 1 12) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 1 12) else d52 (change pattern 1 12)) = d83 pattern
  rw [s5813, s5779]
  rfl
theorem s5815 (pattern : Twelve) : d44 (change pattern 1 12) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 1 12) else d2 (change pattern 1 12)) = d44 pattern
  rw [s5569, s5456]
  rfl
theorem s5816 (pattern : Twelve) : d63 (change pattern 1 12) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 1 12) else d30 (change pattern 1 12)) = d63 pattern
  rw [s5815, s5472]
  rfl
theorem s5817 (pattern : Twelve) : d64 (change pattern 1 12) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 1 12) else d34 (change pattern 1 12)) = d64 pattern
  rw [s5501, s5477]
  rfl
theorem s5818 (pattern : Twelve) : d84 (change pattern 1 12) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 1 12) else d63 (change pattern 1 12)) = d84 pattern
  rw [s5817, s5816]
  rfl
theorem s5819 (pattern : Twelve) : d98 (change pattern 1 12) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 1 12) else d83 (change pattern 1 12)) = d98 pattern
  rw [s5818, s5814]
  rfl
theorem s5820 (pattern : Twelve) : d106 (change pattern 1 12) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 1 12) else d97 (change pattern 1 12)) = d106 pattern
  rw [s5819, s5811]
  rfl
theorem s5821 (pattern : Twelve) : d65 (change pattern 1 12) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 1 12) else d30 (change pattern 1 12)) = d65 pattern
  rw [s5518, s5472]
  rfl
theorem s5822 (pattern : Twelve) : d85 (change pattern 1 12) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 1 12) else d56 (change pattern 1 12)) = d85 pattern
  rw [s5821, s5474]
  rfl
theorem s5823 (pattern : Twelve) : d66 (change pattern 1 12) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 1 12) else d30 (change pattern 1 12)) = d66 pattern
  rw [s5492, s5472]
  rfl
theorem s5824 (pattern : Twelve) : d86 (change pattern 1 12) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 1 12) else d66 (change pattern 1 12)) = d86 pattern
  rw [s5817, s5823]
  rfl
theorem s5825 (pattern : Twelve) : d99 (change pattern 1 12) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 1 12) else d85 (change pattern 1 12)) = d99 pattern
  rw [s5824, s5822]
  rfl
theorem s5826 (pattern : Twelve) : d107 (change pattern 1 12) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 1 12) else d97 (change pattern 1 12)) = d107 pattern
  rw [s5825, s5811]
  rfl
theorem s5827 (pattern : Twelve) : d112 (change pattern 1 12) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 1 12) else d106 (change pattern 1 12)) = d112 pattern
  rw [s5826, s5820]
  rfl
theorem s5828 (pattern : Twelve) : d67 (change pattern 1 12) = d67 pattern := by
  change (if pattern.h then d46 (change pattern 1 12) else d30 (change pattern 1 12)) = d67 pattern
  rw [s5525, s5472]
  rfl
theorem s5829 (pattern : Twelve) : d87 (change pattern 1 12) = d87 pattern := by
  change (if pattern.f then d67 (change pattern 1 12) else d30 (change pattern 1 12)) = d87 pattern
  rw [s5828, s5472]
  rfl
theorem s5830 (pattern : Twelve) : d68 (change pattern 1 12) = d68 pattern := by
  change (if pattern.h then d38 (change pattern 1 12) else d30 (change pattern 1 12)) = d68 pattern
  rw [s5491, s5472]
  rfl
theorem s5831 (pattern : Twelve) : d88 (change pattern 1 12) = d88 pattern := by
  change (if pattern.f then d64 (change pattern 1 12) else d68 (change pattern 1 12)) = d88 pattern
  rw [s5817, s5830]
  rfl
theorem s5832 (pattern : Twelve) : d100 (change pattern 1 12) = d100 pattern := by
  change (if pattern.e then d88 (change pattern 1 12) else d87 (change pattern 1 12)) = d100 pattern
  rw [s5831, s5829]
  rfl
theorem s5833 (pattern : Twelve) : d69 (change pattern 1 12) = d69 pattern := by
  change (if pattern.h then d47 (change pattern 1 12) else d38 (change pattern 1 12)) = d69 pattern
  rw [s5531, s5491]
  rfl
theorem s5834 (pattern : Twelve) : d89 (change pattern 1 12) = d89 pattern := by
  change (if pattern.f then d69 (change pattern 1 12) else d59 (change pattern 1 12)) = d89 pattern
  rw [s5833, s5493]
  rfl
theorem s5835 (pattern : Twelve) : d70 (change pattern 1 12) = d70 pattern := by
  change (if pattern.h then d48 (change pattern 1 12) else d38 (change pattern 1 12)) = d70 pattern
  rw [s5534, s5491]
  rfl
theorem s5836 (pattern : Twelve) : d71 (change pattern 1 12) = d71 pattern := by
  change (if pattern.h then d49 (change pattern 1 12) else d41 (change pattern 1 12)) = d71 pattern
  rw [s5598, s5496]
  rfl
theorem s5837 (pattern : Twelve) : d90 (change pattern 1 12) = d90 pattern := by
  change (if pattern.f then d71 (change pattern 1 12) else d70 (change pattern 1 12)) = d90 pattern
  rw [s5836, s5835]
  rfl
theorem s5838 (pattern : Twelve) : d101 (change pattern 1 12) = d101 pattern := by
  change (if pattern.e then d90 (change pattern 1 12) else d89 (change pattern 1 12)) = d101 pattern
  rw [s5837, s5834]
  rfl
theorem s5839 (pattern : Twelve) : d108 (change pattern 1 12) = d108 pattern := by
  change (if pattern.j then d101 (change pattern 1 12) else d100 (change pattern 1 12)) = d108 pattern
  rw [s5838, s5832]
  rfl
theorem s5840 (pattern : Twelve) : d109 (change pattern 1 12) = d109 pattern := by
  change (if pattern.j then d6 (change pattern 1 12) else d99 (change pattern 1 12)) = d109 pattern
  rw [s5467, s5825]
  rfl
theorem s5841 (pattern : Twelve) : d113 (change pattern 1 12) = d113 pattern := by
  change (if pattern.d then d109 (change pattern 1 12) else d108 (change pattern 1 12)) = d113 pattern
  rw [s5840, s5839]
  rfl
theorem s5842 (pattern : Twelve) : d115 (change pattern 1 12) = d115 pattern := by
  change (if pattern.c then d113 (change pattern 1 12) else d112 (change pattern 1 12)) = d115 pattern
  rw [s5841, s5827]
  rfl
theorem s5843 (pattern : Twelve) : d116 (change pattern 1 12) = d116 pattern := by
  change (if pattern.g then d115 (change pattern 1 12) else d114 (change pattern 1 12)) = d116 pattern
  rw [s5842, s5810]
  rfl
theorem s5844 (pattern : Twelve) : d810 (change pattern 1 12) = d116 pattern := by
  change d116 (change pattern 1 12) = d116 pattern
  exact s5843 pattern
theorem s5845 (pattern : Twelve) : d120 (change pattern 1 12) = d120 pattern := by
  change (if pattern.i then d25 (change pattern 1 12) else d17 (change pattern 1 12)) = d120 pattern
  rw [s5465, s5450]
  rfl
theorem s5846 (pattern : Twelve) : d129 (change pattern 1 12) = d129 pattern := by
  change (if pattern.h then d29 (change pattern 1 12) else d120 (change pattern 1 12)) = d129 pattern
  rw [s5624, s5845]
  rfl
theorem s5847 (pattern : Twelve) : d136 (change pattern 1 12) = d136 pattern := by
  change (if pattern.f then d129 (change pattern 1 12) else d0 (change pattern 1 12)) = d136 pattern
  rw [s5846, s5447]
  rfl
theorem s5848 (pattern : Twelve) : d144 (change pattern 1 12) = d144 pattern := by
  change (if pattern.e then d136 (change pattern 1 12) else d72 (change pattern 1 12)) = d144 pattern
  rw [s5847, s5772]
  rfl
theorem s5849 (pattern : Twelve) : d121 (change pattern 1 12) = d121 pattern := by
  change (if pattern.i then d23 (change pattern 1 12) else d0 (change pattern 1 12)) = d121 pattern
  rw [s5476, s5447]
  rfl
end NetHack.Sokoban21.Diagram
