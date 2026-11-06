/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1680 (p : Pattern) : d29 (change p 193 none) = d0 p := by
  change (if p 192 then d28 (change p 193 none) else d6 (change p 193 none)) = d0 p
  rw [sub1679, sub1678]
  simp only [ite_self]
theorem sub1681 (p : Pattern) : d14 (change p 193 none) = d0 p := by
  change d0 (change p 193 none) = d0 p
  exact sub1677 p
theorem sub1682 (p : Pattern) : d30 (change p 193 none) = d0 p := by
  change (if p 192 then d28 (change p 193 none) else d14 (change p 193 none)) = d0 p
  rw [sub1679, sub1681]
  simp only [ite_self]
theorem sub1683 (p : Pattern) : d31 (change p 193 none) = d0 p := by
  change (if p 168 then d30 (change p 193 none) else d29 (change p 193 none)) = d0 p
  rw [sub1682, sub1680]
  simp only [ite_self]
theorem sub1684 (p : Pattern) : d2 (change p 193 none) = d2 p := by
  rfl
theorem sub1685 (p : Pattern) : d54 (change p 193 none) = d2 p := by
  change d2 (change p 193 none) = d2 p
  exact sub1684 p
theorem sub1686 (p : Pattern) : d587 (change p 193 none) = d2 p := by
  change d2 (change p 193 none) = d2 p
  exact sub1684 p
theorem sub1687 (p : Pattern) : d588 (change p 193 none) = d2 p := by
  change (if p 192 then d587 (change p 193 none) else d54 (change p 193 none)) = d2 p
  rw [sub1686, sub1685]
  simp only [ite_self]
theorem sub1688 (p : Pattern) : d589 (change p 193 none) = d45 p := by
  change (if p 186 then d588 (change p 193 none) else d29 (change p 193 none)) = d45 p
  rw [sub1687, sub1680]
  rfl
theorem sub1689 (p : Pattern) : d259 (change p 193 none) = d2 p := by
  change d2 (change p 193 none) = d2 p
  exact sub1684 p
theorem sub1690 (p : Pattern) : d590 (change p 193 none) = d2 p := by
  change (if p 192 then d587 (change p 193 none) else d259 (change p 193 none)) = d2 p
  rw [sub1686, sub1689]
  simp only [ite_self]
theorem sub1691 (p : Pattern) : d591 (change p 193 none) = d45 p := by
  change (if p 186 then d590 (change p 193 none) else d30 (change p 193 none)) = d45 p
  rw [sub1690, sub1682]
  rfl
theorem sub1692 (p : Pattern) : d592 (change p 193 none) = d45 p := by
  change (if p 168 then d591 (change p 193 none) else d589 (change p 193 none)) = d45 p
  rw [sub1691, sub1688]
  simp only [ite_self]
theorem sub1693 (p : Pattern) : d593 (change p 193 none) = d46 p := by
  change (if p 160 then d592 (change p 193 none) else d31 (change p 193 none)) = d46 p
  rw [sub1692, sub1683]
  rfl
theorem sub1694 (p : Pattern) : d1 (change p 193 none) = d1 p := by
  rfl
theorem sub1695 (p : Pattern) : d8 (change p 193 none) = d8 p := by
  change (if p 271 then d1 (change p 193 none) else d0 (change p 193 none)) = d8 p
  rw [sub1694, sub1677]
  rfl
theorem sub1696 (p : Pattern) : d32 (change p 193 none) = d8 p := by
  change d8 (change p 193 none) = d8 p
  exact sub1695 p
theorem sub1697 (p : Pattern) : d33 (change p 193 none) = d1055 p := by
  change (if p 168 then d32 (change p 193 none) else d30 (change p 193 none)) = d1055 p
  rw [sub1696, sub1682]
  rfl
theorem sub1698 (p : Pattern) : d3 (change p 193 none) = d3 p := by
  rfl
theorem sub1699 (p : Pattern) : d9 (change p 193 none) = d9 p := by
  change (if p 271 then d3 (change p 193 none) else d2 (change p 193 none)) = d9 p
  rw [sub1698, sub1684]
  rfl
theorem sub1700 (p : Pattern) : d594 (change p 193 none) = d9 p := by
  change d9 (change p 193 none) = d9 p
  exact sub1699 p
theorem sub1701 (p : Pattern) : d595 (change p 193 none) = d1056 p := by
  change (if p 186 then d594 (change p 193 none) else d32 (change p 193 none)) = d1056 p
  rw [sub1700, sub1696]
  rfl
theorem sub1702 (p : Pattern) : d596 (change p 193 none) = d1057 p := by
  change (if p 168 then d595 (change p 193 none) else d591 (change p 193 none)) = d1057 p
  rw [sub1701, sub1691]
  rfl
theorem sub1703 (p : Pattern) : d597 (change p 193 none) = d1058 p := by
  change (if p 160 then d596 (change p 193 none) else d33 (change p 193 none)) = d1058 p
  rw [sub1702, sub1697]
  rfl
theorem sub1704 (p : Pattern) : d598 (change p 193 none) = d1059 p := by
  change (if p 141 then d597 (change p 193 none) else d593 (change p 193 none)) = d1059 p
  rw [sub1703, sub1693]
  rfl
theorem sub1705 (p : Pattern) : d599 (change p 193 none) = d2 p := by
  change (if p 168 then d590 (change p 193 none) else d588 (change p 193 none)) = d2 p
  rw [sub1690, sub1687]
  simp only [ite_self]
theorem sub1706 (p : Pattern) : d600 (change p 193 none) = d76 p := by
  change (if p 160 then d599 (change p 193 none) else d31 (change p 193 none)) = d76 p
  rw [sub1705, sub1683]
  rfl
theorem sub1707 (p : Pattern) : d601 (change p 193 none) = d82 p := by
  change (if p 187 then d588 (change p 193 none) else d29 (change p 193 none)) = d82 p
  rw [sub1687, sub1680]
  rfl
theorem sub1708 (p : Pattern) : d602 (change p 193 none) = d83 p := by
  change (if p 186 then d601 (change p 193 none) else d29 (change p 193 none)) = d83 p
  rw [sub1707, sub1680]
  rfl
theorem sub1709 (p : Pattern) : d603 (change p 193 none) = d82 p := by
  change (if p 187 then d590 (change p 193 none) else d30 (change p 193 none)) = d82 p
  rw [sub1690, sub1682]
  rfl
theorem sub1710 (p : Pattern) : d604 (change p 193 none) = d83 p := by
  change (if p 186 then d603 (change p 193 none) else d30 (change p 193 none)) = d83 p
  rw [sub1709, sub1682]
  rfl
theorem sub1711 (p : Pattern) : d605 (change p 193 none) = d83 p := by
  change (if p 168 then d604 (change p 193 none) else d602 (change p 193 none)) = d83 p
  rw [sub1710, sub1708]
  simp only [ite_self]
theorem sub1712 (p : Pattern) : d606 (change p 193 none) = d84 p := by
  change (if p 160 then d599 (change p 193 none) else d605 (change p 193 none)) = d84 p
  rw [sub1705, sub1711]
  rfl
theorem sub1713 (p : Pattern) : d607 (change p 193 none) = d85 p := by
  change (if p 159 then d606 (change p 193 none) else d600 (change p 193 none)) = d85 p
  rw [sub1712, sub1706]
  rfl
theorem sub1714 (p : Pattern) : d608 (change p 193 none) = d162 p := by
  change (if p 158 then d607 (change p 193 none) else d600 (change p 193 none)) = d162 p
  rw [sub1713, sub1706]
  rfl
theorem sub1715 (p : Pattern) : d609 (change p 193 none) = d1060 p := by
  change (if p 168 then d594 (change p 193 none) else d590 (change p 193 none)) = d1060 p
  rw [sub1700, sub1690]
  rfl
theorem sub1716 (p : Pattern) : d610 (change p 193 none) = d1061 p := by
  change (if p 160 then d609 (change p 193 none) else d33 (change p 193 none)) = d1061 p
  rw [sub1715, sub1697]
  rfl
theorem sub1717 (p : Pattern) : d611 (change p 193 none) = d1062 p := by
  change (if p 187 then d594 (change p 193 none) else d32 (change p 193 none)) = d1062 p
  rw [sub1700, sub1696]
  rfl
theorem sub1718 (p : Pattern) : d612 (change p 193 none) = d1063 p := by
  change (if p 186 then d611 (change p 193 none) else d32 (change p 193 none)) = d1063 p
  rw [sub1717, sub1696]
  rfl
theorem sub1719 (p : Pattern) : d613 (change p 193 none) = d1064 p := by
  change (if p 168 then d612 (change p 193 none) else d604 (change p 193 none)) = d1064 p
  rw [sub1718, sub1710]
  rfl
theorem sub1720 (p : Pattern) : d614 (change p 193 none) = d1065 p := by
  change (if p 160 then d609 (change p 193 none) else d613 (change p 193 none)) = d1065 p
  rw [sub1715, sub1719]
  rfl
theorem sub1721 (p : Pattern) : d615 (change p 193 none) = d1066 p := by
  change (if p 159 then d614 (change p 193 none) else d610 (change p 193 none)) = d1066 p
  rw [sub1720, sub1716]
  rfl
theorem sub1722 (p : Pattern) : d616 (change p 193 none) = d1067 p := by
  change (if p 158 then d615 (change p 193 none) else d610 (change p 193 none)) = d1067 p
  rw [sub1721, sub1716]
  rfl
theorem sub1723 (p : Pattern) : d617 (change p 193 none) = d1068 p := by
  change (if p 141 then d616 (change p 193 none) else d608 (change p 193 none)) = d1068 p
  rw [sub1722, sub1714]
  rfl
theorem sub1724 (p : Pattern) : d618 (change p 193 none) = d1069 p := by
  change (if p 134 then d617 (change p 193 none) else d598 (change p 193 none)) = d1069 p
  rw [sub1723, sub1704]
  rfl
theorem sub1725 (p : Pattern) : d619 (change p 193 none) = d48 p := by
  change (if p 158 then d599 (change p 193 none) else d593 (change p 193 none)) = d48 p
  rw [sub1705, sub1693]
  rfl
theorem sub1726 (p : Pattern) : d620 (change p 193 none) = d1070 p := by
  change (if p 158 then d609 (change p 193 none) else d597 (change p 193 none)) = d1070 p
  rw [sub1715, sub1703]
  rfl
theorem sub1727 (p : Pattern) : d621 (change p 193 none) = d1071 p := by
  change (if p 141 then d620 (change p 193 none) else d619 (change p 193 none)) = d1071 p
  rw [sub1726, sub1725]
  rfl
theorem sub1728 (p : Pattern) : d622 (change p 193 none) = d164 p := by
  change (if p 158 then d599 (change p 193 none) else d607 (change p 193 none)) = d164 p
  rw [sub1705, sub1713]
  rfl
theorem sub1729 (p : Pattern) : d623 (change p 193 none) = d1072 p := by
  change (if p 158 then d609 (change p 193 none) else d615 (change p 193 none)) = d1072 p
  rw [sub1715, sub1721]
  rfl
theorem sub1730 (p : Pattern) : d624 (change p 193 none) = d1073 p := by
  change (if p 141 then d623 (change p 193 none) else d622 (change p 193 none)) = d1073 p
  rw [sub1729, sub1728]
  rfl
theorem sub1731 (p : Pattern) : d625 (change p 193 none) = d1074 p := by
  change (if p 134 then d624 (change p 193 none) else d621 (change p 193 none)) = d1074 p
  rw [sub1730, sub1727]
  rfl
theorem sub1732 (p : Pattern) : d626 (change p 193 none) = d1075 p := by
  change (if p 133 then d625 (change p 193 none) else d618 (change p 193 none)) = d1075 p
  rw [sub1731, sub1724]
  rfl
theorem sub1733 (p : Pattern) : d627 (change p 193 none) = d1076 p := by
  change (if p 141 then d609 (change p 193 none) else d599 (change p 193 none)) = d1076 p
  rw [sub1715, sub1705]
  rfl
theorem sub1734 (p : Pattern) : d628 (change p 193 none) = d1077 p := by
  change (if p 133 then d627 (change p 193 none) else d625 (change p 193 none)) = d1077 p
  rw [sub1733, sub1731]
  rfl
theorem sub1735 (p : Pattern) : d629 (change p 193 none) = d1078 p := by
  change (if p 132 then d628 (change p 193 none) else d626 (change p 193 none)) = d1078 p
  rw [sub1734, sub1732]
  rfl
theorem sub1736 (p : Pattern) : d630 (change p 193 none) = d92 p := by
  change (if p 186 then d588 (change p 193 none) else d601 (change p 193 none)) = d92 p
  rw [sub1687, sub1707]
  rfl
theorem sub1737 (p : Pattern) : d631 (change p 193 none) = d92 p := by
  change (if p 186 then d590 (change p 193 none) else d603 (change p 193 none)) = d92 p
  rw [sub1690, sub1709]
  rfl
theorem sub1738 (p : Pattern) : d632 (change p 193 none) = d92 p := by
  change (if p 168 then d631 (change p 193 none) else d630 (change p 193 none)) = d92 p
  rw [sub1737, sub1736]
  simp only [ite_self]
theorem sub1739 (p : Pattern) : d633 (change p 193 none) = d94 p := by
  change (if p 160 then d632 (change p 193 none) else d605 (change p 193 none)) = d94 p
  rw [sub1738, sub1711]
  rfl
theorem sub1740 (p : Pattern) : d634 (change p 193 none) = d100 p := by
  change (if p 159 then d633 (change p 193 none) else d593 (change p 193 none)) = d100 p
  rw [sub1739, sub1693]
  rfl
theorem sub1741 (p : Pattern) : d635 (change p 193 none) = d169 p := by
  change (if p 158 then d634 (change p 193 none) else d593 (change p 193 none)) = d169 p
  rw [sub1740, sub1693]
  rfl
theorem sub1742 (p : Pattern) : d636 (change p 193 none) = d1079 p := by
  change (if p 186 then d594 (change p 193 none) else d611 (change p 193 none)) = d1079 p
  rw [sub1700, sub1717]
  rfl
theorem sub1743 (p : Pattern) : d637 (change p 193 none) = d1080 p := by
  change (if p 168 then d636 (change p 193 none) else d631 (change p 193 none)) = d1080 p
  rw [sub1742, sub1737]
  rfl
theorem sub1744 (p : Pattern) : d638 (change p 193 none) = d1081 p := by
  change (if p 160 then d637 (change p 193 none) else d613 (change p 193 none)) = d1081 p
  rw [sub1743, sub1719]
  rfl
theorem sub1745 (p : Pattern) : d639 (change p 193 none) = d1082 p := by
  change (if p 159 then d638 (change p 193 none) else d597 (change p 193 none)) = d1082 p
  rw [sub1744, sub1703]
  rfl
theorem sub1746 (p : Pattern) : d640 (change p 193 none) = d1083 p := by
  change (if p 158 then d639 (change p 193 none) else d597 (change p 193 none)) = d1083 p
  rw [sub1745, sub1703]
  rfl
theorem sub1747 (p : Pattern) : d641 (change p 193 none) = d1084 p := by
  change (if p 141 then d640 (change p 193 none) else d635 (change p 193 none)) = d1084 p
  rw [sub1746, sub1741]
  rfl
theorem sub1748 (p : Pattern) : d642 (change p 193 none) = d1085 p := by
  change (if p 134 then d627 (change p 193 none) else d641 (change p 193 none)) = d1085 p
  rw [sub1733, sub1747]
  rfl
theorem sub1749 (p : Pattern) : d643 (change p 193 none) = d93 p := by
  change (if p 160 then d632 (change p 193 none) else d31 (change p 193 none)) = d93 p
  rw [sub1738, sub1683]
  rfl
theorem sub1750 (p : Pattern) : d644 (change p 193 none) = d95 p := by
  change (if p 159 then d633 (change p 193 none) else d643 (change p 193 none)) = d95 p
  rw [sub1739, sub1749]
  rfl
theorem sub1751 (p : Pattern) : d645 (change p 193 none) = d171 p := by
  change (if p 158 then d599 (change p 193 none) else d644 (change p 193 none)) = d171 p
  rw [sub1705, sub1750]
  rfl
theorem sub1752 (p : Pattern) : d646 (change p 193 none) = d1086 p := by
  change (if p 160 then d637 (change p 193 none) else d33 (change p 193 none)) = d1086 p
  rw [sub1743, sub1697]
  rfl
theorem sub1753 (p : Pattern) : d647 (change p 193 none) = d1087 p := by
  change (if p 159 then d638 (change p 193 none) else d646 (change p 193 none)) = d1087 p
  rw [sub1744, sub1752]
  rfl
theorem sub1754 (p : Pattern) : d648 (change p 193 none) = d1088 p := by
  change (if p 158 then d609 (change p 193 none) else d647 (change p 193 none)) = d1088 p
  rw [sub1715, sub1753]
  rfl
theorem sub1755 (p : Pattern) : d649 (change p 193 none) = d1089 p := by
  change (if p 141 then d648 (change p 193 none) else d645 (change p 193 none)) = d1089 p
  rw [sub1754, sub1751]
  rfl
theorem sub1756 (p : Pattern) : d650 (change p 193 none) = d1090 p := by
  change (if p 134 then d627 (change p 193 none) else d649 (change p 193 none)) = d1090 p
  rw [sub1733, sub1755]
  rfl
theorem sub1757 (p : Pattern) : d651 (change p 193 none) = d1091 p := by
  change (if p 133 then d650 (change p 193 none) else d642 (change p 193 none)) = d1091 p
  rw [sub1756, sub1748]
  rfl
theorem sub1758 (p : Pattern) : d652 (change p 193 none) = d174 p := by
  change (if p 158 then d599 (change p 193 none) else d634 (change p 193 none)) = d174 p
  rw [sub1705, sub1740]
  rfl
theorem sub1759 (p : Pattern) : d653 (change p 193 none) = d1092 p := by
  change (if p 158 then d609 (change p 193 none) else d639 (change p 193 none)) = d1092 p
  rw [sub1715, sub1745]
  rfl
theorem sub1760 (p : Pattern) : d654 (change p 193 none) = d1093 p := by
  change (if p 141 then d653 (change p 193 none) else d652 (change p 193 none)) = d1093 p
  rw [sub1759, sub1758]
  rfl
theorem sub1761 (p : Pattern) : d655 (change p 193 none) = d1094 p := by
  change (if p 134 then d627 (change p 193 none) else d654 (change p 193 none)) = d1094 p
  rw [sub1733, sub1760]
  rfl
theorem sub1762 (p : Pattern) : d656 (change p 193 none) = d1095 p := by
  change (if p 133 then d627 (change p 193 none) else d655 (change p 193 none)) = d1095 p
  rw [sub1733, sub1761]
  rfl
theorem sub1763 (p : Pattern) : d657 (change p 193 none) = d1096 p := by
  change (if p 132 then d656 (change p 193 none) else d651 (change p 193 none)) = d1096 p
  rw [sub1762, sub1757]
  rfl
theorem sub1764 (p : Pattern) : d658 (change p 193 none) = d1097 p := by
  change (if p 108 then d657 (change p 193 none) else d629 (change p 193 none)) = d1097 p
  rw [sub1763, sub1735]
  rfl
theorem sub1765 (p : Pattern) : d0 (change p 158 (some 132)) = d0 p := by
  rfl
theorem sub1766 (p : Pattern) : d2 (change p 158 (some 132)) = d2 p := by
  rfl
theorem sub1767 (p : Pattern) : d6 (change p 158 (some 132)) = d6 p := by
  change (if p 193 then d2 (change p 158 (some 132)) else d0 (change p 158 (some 132))) = d6 p
  rw [sub1766, sub1765]
  rfl
theorem sub1768 (p : Pattern) : d7 (change p 158 (some 132)) = d7 p := by
  change (if p 192 then d6 (change p 158 (some 132)) else d0 (change p 158 (some 132))) = d7 p
  rw [sub1767, sub1765]
  rfl
theorem sub1769 (p : Pattern) : d4 (change p 158 (some 132)) = d4 p := by
  rfl
theorem sub1770 (p : Pattern) : d54 (change p 158 (some 132)) = d54 p := by
  change (if p 193 then d4 (change p 158 (some 132)) else d2 (change p 158 (some 132))) = d54 p
  rw [sub1769, sub1766]
  rfl
theorem sub1771 (p : Pattern) : d55 (change p 158 (some 132)) = d55 p := by
  change (if p 192 then d54 (change p 158 (some 132)) else d2 (change p 158 (some 132))) = d55 p
  rw [sub1770, sub1766]
  rfl
theorem sub1772 (p : Pattern) : d56 (change p 158 (some 132)) = d56 p := by
  change (if p 186 then d55 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d56 p
  rw [sub1771, sub1768]
  rfl
theorem sub1773 (p : Pattern) : d57 (change p 158 (some 132)) = d57 p := by
  change (if p 160 then d56 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d57 p
  rw [sub1772, sub1768]
  rfl
theorem sub1774 (p : Pattern) : d68 (change p 158 (some 132)) = d57 p := by
  change d57 (change p 158 (some 132)) = d57 p
  exact sub1773 p
theorem sub1775 (p : Pattern) : d1 (change p 158 (some 132)) = d1 p := by
  rfl
theorem sub1776 (p : Pattern) : d8 (change p 158 (some 132)) = d8 p := by
  change (if p 271 then d1 (change p 158 (some 132)) else d0 (change p 158 (some 132))) = d8 p
  rw [sub1775, sub1765]
  rfl
theorem sub1777 (p : Pattern) : d3 (change p 158 (some 132)) = d3 p := by
  rfl
theorem sub1778 (p : Pattern) : d9 (change p 158 (some 132)) = d9 p := by
  change (if p 271 then d3 (change p 158 (some 132)) else d2 (change p 158 (some 132))) = d9 p
  rw [sub1777, sub1766]
  rfl
theorem sub1779 (p : Pattern) : d10 (change p 158 (some 132)) = d10 p := by
  change (if p 193 then d9 (change p 158 (some 132)) else d8 (change p 158 (some 132))) = d10 p
  rw [sub1778, sub1776]
  rfl
theorem sub1780 (p : Pattern) : d11 (change p 158 (some 132)) = d11 p := by
  change (if p 192 then d10 (change p 158 (some 132)) else d8 (change p 158 (some 132))) = d11 p
  rw [sub1779, sub1776]
  rfl
theorem sub1781 (p : Pattern) : d12 (change p 158 (some 132)) = d12 p := by
  change (if p 168 then d11 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d12 p
  rw [sub1780, sub1768]
  rfl
theorem sub1782 (p : Pattern) : d5 (change p 158 (some 132)) = d5 p := by
  rfl
theorem sub1783 (p : Pattern) : d58 (change p 158 (some 132)) = d58 p := by
  change (if p 271 then d5 (change p 158 (some 132)) else d4 (change p 158 (some 132))) = d58 p
  rw [sub1782, sub1769]
  rfl
theorem sub1784 (p : Pattern) : d59 (change p 158 (some 132)) = d59 p := by
  change (if p 193 then d58 (change p 158 (some 132)) else d9 (change p 158 (some 132))) = d59 p
  rw [sub1783, sub1778]
  rfl
theorem sub1785 (p : Pattern) : d60 (change p 158 (some 132)) = d60 p := by
  change (if p 192 then d59 (change p 158 (some 132)) else d9 (change p 158 (some 132))) = d60 p
  rw [sub1784, sub1778]
  rfl
theorem sub1786 (p : Pattern) : d61 (change p 158 (some 132)) = d61 p := by
  change (if p 186 then d60 (change p 158 (some 132)) else d11 (change p 158 (some 132))) = d61 p
  rw [sub1785, sub1780]
  rfl
theorem sub1787 (p : Pattern) : d62 (change p 158 (some 132)) = d62 p := by
  change (if p 168 then d61 (change p 158 (some 132)) else d56 (change p 158 (some 132))) = d62 p
  rw [sub1786, sub1772]
  rfl
theorem sub1788 (p : Pattern) : d63 (change p 158 (some 132)) = d63 p := by
  change (if p 160 then d62 (change p 158 (some 132)) else d12 (change p 158 (some 132))) = d63 p
  rw [sub1787, sub1781]
  rfl
theorem sub1789 (p : Pattern) : d69 (change p 158 (some 132)) = d63 p := by
  change d63 (change p 158 (some 132)) = d63 p
  exact sub1788 p
theorem sub1790 (p : Pattern) : d70 (change p 158 (some 132)) = d64 p := by
  change (if p 141 then d69 (change p 158 (some 132)) else d68 (change p 158 (some 132))) = d64 p
  rw [sub1789, sub1774]
  rfl
theorem sub1791 (p : Pattern) : d106 (change p 158 (some 132)) = d106 p := by
  change (if p 160 then d55 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d106 p
  rw [sub1771, sub1768]
  rfl
theorem sub1792 (p : Pattern) : d119 (change p 158 (some 132)) = d119 p := by
  change (if p 187 then d55 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d119 p
  rw [sub1771, sub1768]
  rfl
theorem sub1793 (p : Pattern) : d120 (change p 158 (some 132)) = d120 p := by
  change (if p 186 then d119 (change p 158 (some 132)) else d7 (change p 158 (some 132))) = d120 p
  rw [sub1792, sub1768]
  rfl
theorem sub1794 (p : Pattern) : d121 (change p 158 (some 132)) = d121 p := by
  change (if p 160 then d55 (change p 158 (some 132)) else d120 (change p 158 (some 132))) = d121 p
  rw [sub1771, sub1793]
  rfl
theorem sub1795 (p : Pattern) : d122 (change p 158 (some 132)) = d122 p := by
  change (if p 159 then d121 (change p 158 (some 132)) else d106 (change p 158 (some 132))) = d122 p
  rw [sub1794, sub1791]
  rfl
theorem sub1796 (p : Pattern) : d181 (change p 158 (some 132)) = d122 p := by
  change d122 (change p 158 (some 132)) = d122 p
  exact sub1795 p
theorem sub1797 (p : Pattern) : d65 (change p 158 (some 132)) = d65 p := by
  change (if p 168 then d60 (change p 158 (some 132)) else d55 (change p 158 (some 132))) = d65 p
  rw [sub1785, sub1771]
  rfl
theorem sub1798 (p : Pattern) : d109 (change p 158 (some 132)) = d109 p := by
  change (if p 160 then d65 (change p 158 (some 132)) else d12 (change p 158 (some 132))) = d109 p
  rw [sub1797, sub1781]
  rfl
theorem sub1799 (p : Pattern) : d125 (change p 158 (some 132)) = d125 p := by
  change (if p 187 then d60 (change p 158 (some 132)) else d11 (change p 158 (some 132))) = d125 p
  rw [sub1785, sub1780]
  rfl
end NetHack.Sokoban12CostPartition
