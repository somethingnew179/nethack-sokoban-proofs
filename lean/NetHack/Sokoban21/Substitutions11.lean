/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions10
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1650 (pattern : Twelve) : d92 (change pattern 12 10) = d2071 pattern := by
  change (if pattern.e then d75 (change pattern 12 10) else d74 (change pattern 12 10)) = d2071 pattern
  rw [s1649, s1642]
  rfl
theorem s1651 (pattern : Twelve) : d102 (change pattern 12 10) = d2072 pattern := by
  change (if pattern.j then d92 (change pattern 12 10) else d91 (change pattern 12 10)) = d2072 pattern
  rw [s1650, s1630]
  rfl
theorem s1652 (pattern : Twelve) : d76 (change pattern 12 10) = d2063 pattern := by
  change (if pattern.f then d55 (change pattern 12 10) else d0 (change pattern 12 10)) = d2063 pattern
  rw [s1648, s1611]
  rfl
theorem s1653 (pattern : Twelve) : d93 (change pattern 12 10) = d2064 pattern := by
  change (if pattern.e then d76 (change pattern 12 10) else d72 (change pattern 12 10)) = d2064 pattern
  rw [s1652, s1618]
  rfl
theorem s1654 (pattern : Twelve) : d35 (change pattern 12 10) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d0 (change pattern 12 10)) = d35 pattern
  rw [s1626, s1611]
  rfl
theorem s1655 (pattern : Twelve) : d56 (change pattern 12 10) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 12 10) else d30 (change pattern 12 10)) = d56 pattern
  rw [s1654, s1631]
  rfl
theorem s1656 (pattern : Twelve) : d36 (change pattern 12 10) = d2073 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d17 (change pattern 12 10)) = d2073 pattern
  rw [s1626, s1615]
  rfl
theorem s1657 (pattern : Twelve) : d57 (change pattern 12 10) = d2074 pattern := by
  change (if pattern.h then d36 (change pattern 12 10) else d30 (change pattern 12 10)) = d2074 pattern
  rw [s1656, s1631]
  rfl
theorem s1658 (pattern : Twelve) : d77 (change pattern 12 10) = d2075 pattern := by
  change (if pattern.f then d57 (change pattern 12 10) else d56 (change pattern 12 10)) = d2075 pattern
  rw [s1657, s1655]
  rfl
theorem s1659 (pattern : Twelve) : d78 (change pattern 12 10) = d2070 pattern := by
  change (if pattern.f then d55 (change pattern 12 10) else d56 (change pattern 12 10)) = d2070 pattern
  rw [s1648, s1655]
  rfl
theorem s1660 (pattern : Twelve) : d94 (change pattern 12 10) = d2076 pattern := by
  change (if pattern.e then d78 (change pattern 12 10) else d77 (change pattern 12 10)) = d2076 pattern
  rw [s1659, s1658]
  rfl
theorem s1661 (pattern : Twelve) : d103 (change pattern 12 10) = d2077 pattern := by
  change (if pattern.j then d94 (change pattern 12 10) else d93 (change pattern 12 10)) = d2077 pattern
  rw [s1660, s1653]
  rfl
theorem s1662 (pattern : Twelve) : d110 (change pattern 12 10) = d2078 pattern := by
  change (if pattern.d then d103 (change pattern 12 10) else d102 (change pattern 12 10)) = d2078 pattern
  rw [s1661, s1651]
  rfl
theorem s1663 (pattern : Twelve) : d37 (change pattern 12 10) = d2079 pattern := by
  change (if pattern.i then d3 (change pattern 12 10) else d17 (change pattern 12 10)) = d2079 pattern
  rw [s1620, s1615]
  rfl
theorem s1664 (pattern : Twelve) : d58 (change pattern 12 10) = d2080 pattern := by
  change (if pattern.h then d37 (change pattern 12 10) else d30 (change pattern 12 10)) = d2080 pattern
  rw [s1663, s1631]
  rfl
theorem s1665 (pattern : Twelve) : d79 (change pattern 12 10) = d2081 pattern := by
  change (if pattern.f then d58 (change pattern 12 10) else d30 (change pattern 12 10)) = d2081 pattern
  rw [s1664, s1631]
  rfl
theorem s1666 (pattern : Twelve) : d80 (change pattern 12 10) = d2082 pattern := by
  change (if pattern.f then d55 (change pattern 12 10) else d30 (change pattern 12 10)) = d2082 pattern
  rw [s1648, s1631]
  rfl
theorem s1667 (pattern : Twelve) : d95 (change pattern 12 10) = d2083 pattern := by
  change (if pattern.e then d80 (change pattern 12 10) else d79 (change pattern 12 10)) = d2083 pattern
  rw [s1666, s1665]
  rfl
theorem s1668 (pattern : Twelve) : d38 (change pattern 12 10) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 12 10) else d2 (change pattern 12 10)) = d38 pattern
  rw [s1632, s1619]
  rfl
theorem s1669 (pattern : Twelve) : d39 (change pattern 12 10) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d2 (change pattern 12 10)) = d39 pattern
  rw [s1626, s1619]
  rfl
theorem s1670 (pattern : Twelve) : d59 (change pattern 12 10) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 12 10) else d38 (change pattern 12 10)) = d59 pattern
  rw [s1669, s1668]
  rfl
theorem s1671 (pattern : Twelve) : d40 (change pattern 12 10) = d2084 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d23 (change pattern 12 10)) = d2084 pattern
  rw [s1626, s1646]
  rfl
theorem s1672 (pattern : Twelve) : d60 (change pattern 12 10) = d2085 pattern := by
  change (if pattern.h then d40 (change pattern 12 10) else d38 (change pattern 12 10)) = d2085 pattern
  rw [s1671, s1668]
  rfl
theorem s1673 (pattern : Twelve) : d81 (change pattern 12 10) = d2086 pattern := by
  change (if pattern.f then d60 (change pattern 12 10) else d59 (change pattern 12 10)) = d2086 pattern
  rw [s1672, s1670]
  rfl
theorem s1674 (pattern : Twelve) : d15 (change pattern 12 10) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 12 10) else d4 (change pattern 12 10)) = d15 pattern
  rw [s1637, s1632]
  rfl
theorem s1675 (pattern : Twelve) : d24 (change pattern 12 10) = d15 pattern := by
  change d15 (change pattern 12 10) = d15 pattern
  exact s1674 pattern
theorem s1676 (pattern : Twelve) : d41 (change pattern 12 10) = d2087 pattern := by
  change (if pattern.i then d24 (change pattern 12 10) else d23 (change pattern 12 10)) = d2087 pattern
  rw [s1675, s1646]
  rfl
theorem s1677 (pattern : Twelve) : d12 (change pattern 12 10) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 10) else d3 (change pattern 12 10)) = d12 pattern
  rw [s1637, s1620]
  rfl
theorem s1678 (pattern : Twelve) : d25 (change pattern 12 10) = d12 pattern := by
  change d12 (change pattern 12 10) = d12 pattern
  exact s1677 pattern
theorem s1679 (pattern : Twelve) : d42 (change pattern 12 10) = d2088 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d25 (change pattern 12 10)) = d2088 pattern
  rw [s1626, s1678]
  rfl
theorem s1680 (pattern : Twelve) : d61 (change pattern 12 10) = d2089 pattern := by
  change (if pattern.h then d42 (change pattern 12 10) else d41 (change pattern 12 10)) = d2089 pattern
  rw [s1679, s1676]
  rfl
theorem s1681 (pattern : Twelve) : d82 (change pattern 12 10) = d2090 pattern := by
  change (if pattern.f then d61 (change pattern 12 10) else d59 (change pattern 12 10)) = d2090 pattern
  rw [s1680, s1670]
  rfl
theorem s1682 (pattern : Twelve) : d96 (change pattern 12 10) = d2091 pattern := by
  change (if pattern.e then d82 (change pattern 12 10) else d81 (change pattern 12 10)) = d2091 pattern
  rw [s1681, s1673]
  rfl
theorem s1683 (pattern : Twelve) : d104 (change pattern 12 10) = d2092 pattern := by
  change (if pattern.j then d96 (change pattern 12 10) else d95 (change pattern 12 10)) = d2092 pattern
  rw [s1682, s1667]
  rfl
theorem s1684 (pattern : Twelve) : d105 (change pattern 12 10) = d2093 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d94 (change pattern 12 10)) = d2093 pattern
  rw [s1626, s1660]
  rfl
theorem s1685 (pattern : Twelve) : d111 (change pattern 12 10) = d2094 pattern := by
  change (if pattern.d then d105 (change pattern 12 10) else d104 (change pattern 12 10)) = d2094 pattern
  rw [s1684, s1683]
  rfl
theorem s1686 (pattern : Twelve) : d114 (change pattern 12 10) = d2095 pattern := by
  change (if pattern.c then d111 (change pattern 12 10) else d110 (change pattern 12 10)) = d2095 pattern
  rw [s1685, s1662]
  rfl
theorem s1687 (pattern : Twelve) : d120 (change pattern 12 10) = d2096 pattern := by
  change (if pattern.i then d25 (change pattern 12 10) else d17 (change pattern 12 10)) = d2096 pattern
  rw [s1678, s1615]
  rfl
theorem s1688 (pattern : Twelve) : d129 (change pattern 12 10) = d2097 pattern := by
  change (if pattern.h then d29 (change pattern 12 10) else d120 (change pattern 12 10)) = d2097 pattern
  rw [s1627, s1687]
  rfl
theorem s1689 (pattern : Twelve) : d136 (change pattern 12 10) = d2098 pattern := by
  change (if pattern.f then d129 (change pattern 12 10) else d0 (change pattern 12 10)) = d2098 pattern
  rw [s1688, s1611]
  rfl
theorem s1690 (pattern : Twelve) : d144 (change pattern 12 10) = d2099 pattern := by
  change (if pattern.e then d136 (change pattern 12 10) else d72 (change pattern 12 10)) = d2099 pattern
  rw [s1689, s1618]
  rfl
theorem s1691 (pattern : Twelve) : d121 (change pattern 12 10) = d2100 pattern := by
  change (if pattern.i then d23 (change pattern 12 10) else d0 (change pattern 12 10)) = d2100 pattern
  rw [s1646, s1611]
  rfl
theorem s1692 (pattern : Twelve) : d130 (change pattern 12 10) = d2101 pattern := by
  change (if pattern.h then d36 (change pattern 12 10) else d121 (change pattern 12 10)) = d2101 pattern
  rw [s1656, s1691]
  rfl
theorem s1693 (pattern : Twelve) : d137 (change pattern 12 10) = d2102 pattern := by
  change (if pattern.f then d130 (change pattern 12 10) else d52 (change pattern 12 10)) = d2102 pattern
  rw [s1692, s1636]
  rfl
theorem s1694 (pattern : Twelve) : d138 (change pattern 12 10) = d2103 pattern := by
  change (if pattern.f then d129 (change pattern 12 10) else d56 (change pattern 12 10)) = d2103 pattern
  rw [s1688, s1655]
  rfl
theorem s1695 (pattern : Twelve) : d145 (change pattern 12 10) = d2104 pattern := by
  change (if pattern.e then d138 (change pattern 12 10) else d137 (change pattern 12 10)) = d2104 pattern
  rw [s1694, s1693]
  rfl
theorem s1696 (pattern : Twelve) : d149 (change pattern 12 10) = d2105 pattern := by
  change (if pattern.j then d145 (change pattern 12 10) else d144 (change pattern 12 10)) = d2105 pattern
  rw [s1695, s1690]
  rfl
theorem s1697 (pattern : Twelve) : d139 (change pattern 12 10) = d2106 pattern := by
  change (if pattern.f then d130 (change pattern 12 10) else d56 (change pattern 12 10)) = d2106 pattern
  rw [s1692, s1655]
  rfl
theorem s1698 (pattern : Twelve) : d146 (change pattern 12 10) = d2107 pattern := by
  change (if pattern.e then d138 (change pattern 12 10) else d139 (change pattern 12 10)) = d2107 pattern
  rw [s1694, s1697]
  rfl
theorem s1699 (pattern : Twelve) : d150 (change pattern 12 10) = d2108 pattern := by
  change (if pattern.j then d146 (change pattern 12 10) else d144 (change pattern 12 10)) = d2108 pattern
  rw [s1698, s1690]
  rfl
theorem s1700 (pattern : Twelve) : d153 (change pattern 12 10) = d2109 pattern := by
  change (if pattern.d then d150 (change pattern 12 10) else d149 (change pattern 12 10)) = d2109 pattern
  rw [s1699, s1696]
  rfl
theorem s1701 (pattern : Twelve) : d122 (change pattern 12 10) = d2110 pattern := by
  change (if pattern.i then d4 (change pattern 12 10) else d17 (change pattern 12 10)) = d2110 pattern
  rw [s1632, s1615]
  rfl
theorem s1702 (pattern : Twelve) : d131 (change pattern 12 10) = d2111 pattern := by
  change (if pattern.h then d122 (change pattern 12 10) else d121 (change pattern 12 10)) = d2111 pattern
  rw [s1701, s1691]
  rfl
theorem s1703 (pattern : Twelve) : d140 (change pattern 12 10) = d2112 pattern := by
  change (if pattern.f then d131 (change pattern 12 10) else d30 (change pattern 12 10)) = d2112 pattern
  rw [s1702, s1631]
  rfl
theorem s1704 (pattern : Twelve) : d123 (change pattern 12 10) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 12 10) else d0 (change pattern 12 10)) = d123 pattern
  rw [s1620, s1611]
  rfl
theorem s1705 (pattern : Twelve) : d132 (change pattern 12 10) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 12 10) else d30 (change pattern 12 10)) = d132 pattern
  rw [s1704, s1631]
  rfl
theorem s1706 (pattern : Twelve) : d141 (change pattern 12 10) = d2113 pattern := by
  change (if pattern.f then d129 (change pattern 12 10) else d132 (change pattern 12 10)) = d2113 pattern
  rw [s1688, s1705]
  rfl
theorem s1707 (pattern : Twelve) : d147 (change pattern 12 10) = d2114 pattern := by
  change (if pattern.e then d141 (change pattern 12 10) else d140 (change pattern 12 10)) = d2114 pattern
  rw [s1706, s1703]
  rfl
theorem s1708 (pattern : Twelve) : d118 (change pattern 12 10) = d14 pattern := by
  change d14 (change pattern 12 10) = d14 pattern
  exact s1638 pattern
theorem s1709 (pattern : Twelve) : d124 (change pattern 12 10) = d2115 pattern := by
  change (if pattern.i then d118 (change pattern 12 10) else d2 (change pattern 12 10)) = d2115 pattern
  rw [s1708, s1619]
  rfl
theorem s1710 (pattern : Twelve) : d117 (change pattern 12 10) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 12 10) else d3 (change pattern 12 10)) = d117 pattern
  rw [s1632, s1620]
  rfl
theorem s1711 (pattern : Twelve) : d119 (change pattern 12 10) = d117 pattern := by
  change d117 (change pattern 12 10) = d117 pattern
  exact s1710 pattern
theorem s1712 (pattern : Twelve) : d125 (change pattern 12 10) = d2116 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d119 (change pattern 12 10)) = d2116 pattern
  rw [s1626, s1711]
  rfl
theorem s1713 (pattern : Twelve) : d133 (change pattern 12 10) = d2117 pattern := by
  change (if pattern.h then d125 (change pattern 12 10) else d124 (change pattern 12 10)) = d2117 pattern
  rw [s1712, s1709]
  rfl
theorem s1714 (pattern : Twelve) : d142 (change pattern 12 10) = d2118 pattern := by
  change (if pattern.f then d133 (change pattern 12 10) else d59 (change pattern 12 10)) = d2118 pattern
  rw [s1713, s1670]
  rfl
theorem s1715 (pattern : Twelve) : d126 (change pattern 12 10) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 12 10) else d2 (change pattern 12 10)) = d126 pattern
  rw [s1637, s1619]
  rfl
theorem s1716 (pattern : Twelve) : d47 (change pattern 12 10) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d3 (change pattern 12 10)) = d47 pattern
  rw [s1626, s1620]
  rfl
theorem s1717 (pattern : Twelve) : d134 (change pattern 12 10) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 12 10) else d126 (change pattern 12 10)) = d134 pattern
  rw [s1716, s1715]
  rfl
theorem s1718 (pattern : Twelve) : d127 (change pattern 12 10) = d2084 pattern := by
  change (if pattern.i then d22 (change pattern 12 10) else d23 (change pattern 12 10)) = d2084 pattern
  rw [s1643, s1646]
  rfl
theorem s1719 (pattern : Twelve) : d128 (change pattern 12 10) = d2119 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d20 (change pattern 12 10)) = d2119 pattern
  rw [s1626, s1634]
  rfl
theorem s1720 (pattern : Twelve) : d135 (change pattern 12 10) = d2120 pattern := by
  change (if pattern.h then d128 (change pattern 12 10) else d127 (change pattern 12 10)) = d2120 pattern
  rw [s1719, s1718]
  rfl
theorem s1721 (pattern : Twelve) : d143 (change pattern 12 10) = d2121 pattern := by
  change (if pattern.f then d135 (change pattern 12 10) else d134 (change pattern 12 10)) = d2121 pattern
  rw [s1720, s1717]
  rfl
theorem s1722 (pattern : Twelve) : d148 (change pattern 12 10) = d2122 pattern := by
  change (if pattern.e then d143 (change pattern 12 10) else d142 (change pattern 12 10)) = d2122 pattern
  rw [s1721, s1714]
  rfl
theorem s1723 (pattern : Twelve) : d151 (change pattern 12 10) = d2123 pattern := by
  change (if pattern.j then d148 (change pattern 12 10) else d147 (change pattern 12 10)) = d2123 pattern
  rw [s1722, s1707]
  rfl
theorem s1724 (pattern : Twelve) : d152 (change pattern 12 10) = d2124 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d146 (change pattern 12 10)) = d2124 pattern
  rw [s1626, s1698]
  rfl
theorem s1725 (pattern : Twelve) : d154 (change pattern 12 10) = d2125 pattern := by
  change (if pattern.d then d152 (change pattern 12 10) else d151 (change pattern 12 10)) = d2125 pattern
  rw [s1724, s1723]
  rfl
theorem s1726 (pattern : Twelve) : d155 (change pattern 12 10) = d2126 pattern := by
  change (if pattern.c then d154 (change pattern 12 10) else d153 (change pattern 12 10)) = d2126 pattern
  rw [s1725, s1700]
  rfl
theorem s1727 (pattern : Twelve) : d156 (change pattern 12 10) = d2127 pattern := by
  change (if pattern.a then d155 (change pattern 12 10) else d114 (change pattern 12 10)) = d2127 pattern
  rw [s1726, s1686]
  rfl
theorem s1728 (pattern : Twelve) : d814 (change pattern 12 10) = d1 pattern := by
  change d1 (change pattern 12 10) = d1 pattern
  exact s1612 pattern
theorem s1729 (pattern : Twelve) : d816 (change pattern 12 10) = d1 pattern := by
  change (if pattern.i then d1 (change pattern 12 10) else d814 (change pattern 12 10)) = d1 pattern
  rw [s1612, s1728]
  simp only [ite_self]
theorem s1730 (pattern : Twelve) : d824 (change pattern 12 10) = d2128 pattern := by
  change (if pattern.h then d816 (change pattern 12 10) else d27 (change pattern 12 10)) = d2128 pattern
  rw [s1729, s1616]
  rfl
theorem s1731 (pattern : Twelve) : d838 (change pattern 12 10) = d2129 pattern := by
  change (if pattern.f then d824 (change pattern 12 10) else d0 (change pattern 12 10)) = d2129 pattern
  rw [s1730, s1611]
  rfl
theorem s1732 (pattern : Twelve) : d817 (change pattern 12 10) = d2130 pattern := by
  change (if pattern.i then d25 (change pattern 12 10) else d19 (change pattern 12 10)) = d2130 pattern
  rw [s1678, s1625]
  rfl
theorem s1733 (pattern : Twelve) : d825 (change pattern 12 10) = d2131 pattern := by
  change (if pattern.h then d42 (change pattern 12 10) else d817 (change pattern 12 10)) = d2131 pattern
  rw [s1679, s1732]
  rfl
theorem s1734 (pattern : Twelve) : d839 (change pattern 12 10) = d2132 pattern := by
  change (if pattern.f then d825 (change pattern 12 10) else d17 (change pattern 12 10)) = d2132 pattern
  rw [s1733, s1615]
  rfl
theorem s1735 (pattern : Twelve) : d853 (change pattern 12 10) = d2133 pattern := by
  change (if pattern.e then d839 (change pattern 12 10) else d838 (change pattern 12 10)) = d2133 pattern
  rw [s1734, s1731]
  rfl
theorem s1736 (pattern : Twelve) : d818 (change pattern 12 10) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d814 (change pattern 12 10)) = d45 pattern
  rw [s1626, s1728]
  rfl
theorem s1737 (pattern : Twelve) : d826 (change pattern 12 10) = d2134 pattern := by
  change (if pattern.h then d818 (change pattern 12 10) else d34 (change pattern 12 10)) = d2134 pattern
  rw [s1736, s1647]
  rfl
theorem s1738 (pattern : Twelve) : d840 (change pattern 12 10) = d2135 pattern := by
  change (if pattern.f then d826 (change pattern 12 10) else d56 (change pattern 12 10)) = d2135 pattern
  rw [s1737, s1655]
  rfl
theorem s1739 (pattern : Twelve) : d827 (change pattern 12 10) = d2136 pattern := by
  change (if pattern.h then d36 (change pattern 12 10) else d34 (change pattern 12 10)) = d2136 pattern
  rw [s1656, s1647]
  rfl
theorem s1740 (pattern : Twelve) : d841 (change pattern 12 10) = d2137 pattern := by
  change (if pattern.f then d825 (change pattern 12 10) else d827 (change pattern 12 10)) = d2137 pattern
  rw [s1733, s1739]
  rfl
theorem s1741 (pattern : Twelve) : d854 (change pattern 12 10) = d2138 pattern := by
  change (if pattern.e then d841 (change pattern 12 10) else d840 (change pattern 12 10)) = d2138 pattern
  rw [s1740, s1738]
  rfl
theorem s1742 (pattern : Twelve) : d861 (change pattern 12 10) = d2139 pattern := by
  change (if pattern.j then d854 (change pattern 12 10) else d853 (change pattern 12 10)) = d2139 pattern
  rw [s1741, s1735]
  rfl
theorem s1743 (pattern : Twelve) : d819 (change pattern 12 10) = d46 pattern := by
  change (if pattern.i then d3 (change pattern 12 10) else d814 (change pattern 12 10)) = d46 pattern
  rw [s1620, s1728]
  rfl
theorem s1744 (pattern : Twelve) : d828 (change pattern 12 10) = d2140 pattern := by
  change (if pattern.h then d819 (change pattern 12 10) else d34 (change pattern 12 10)) = d2140 pattern
  rw [s1743, s1647]
  rfl
theorem s1745 (pattern : Twelve) : d842 (change pattern 12 10) = d2141 pattern := by
  change (if pattern.f then d828 (change pattern 12 10) else d30 (change pattern 12 10)) = d2141 pattern
  rw [s1744, s1631]
  rfl
theorem s1746 (pattern : Twelve) : d843 (change pattern 12 10) = d2142 pattern := by
  change (if pattern.f then d825 (change pattern 12 10) else d34 (change pattern 12 10)) = d2142 pattern
  rw [s1733, s1647]
  rfl
theorem s1747 (pattern : Twelve) : d855 (change pattern 12 10) = d2143 pattern := by
  change (if pattern.e then d843 (change pattern 12 10) else d842 (change pattern 12 10)) = d2143 pattern
  rw [s1746, s1745]
  rfl
theorem s1748 (pattern : Twelve) : d815 (change pattern 12 10) = d3 pattern := by
  change d3 (change pattern 12 10) = d3 pattern
  exact s1620 pattern
theorem s1749 (pattern : Twelve) : d820 (change pattern 12 10) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d815 (change pattern 12 10)) = d47 pattern
  rw [s1626, s1748]
  rfl
theorem s1750 (pattern : Twelve) : d829 (change pattern 12 10) = d2144 pattern := by
  change (if pattern.h then d820 (change pattern 12 10) else d41 (change pattern 12 10)) = d2144 pattern
  rw [s1749, s1676]
  rfl
theorem s1751 (pattern : Twelve) : d844 (change pattern 12 10) = d2145 pattern := by
  change (if pattern.f then d829 (change pattern 12 10) else d59 (change pattern 12 10)) = d2145 pattern
  rw [s1750, s1670]
  rfl
theorem s1752 (pattern : Twelve) : d830 (change pattern 12 10) = d2146 pattern := by
  change (if pattern.h then d40 (change pattern 12 10) else d41 (change pattern 12 10)) = d2146 pattern
  rw [s1671, s1676]
  rfl
theorem s1753 (pattern : Twelve) : d821 (change pattern 12 10) = d2147 pattern := by
  change (if pattern.i then d21 (change pattern 12 10) else d25 (change pattern 12 10)) = d2147 pattern
  rw [s1639, s1678]
  rfl
theorem s1754 (pattern : Twelve) : d822 (change pattern 12 10) = d2148 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d21 (change pattern 12 10)) = d2148 pattern
  rw [s1626, s1639]
  rfl
theorem s1755 (pattern : Twelve) : d831 (change pattern 12 10) = d2149 pattern := by
  change (if pattern.h then d822 (change pattern 12 10) else d821 (change pattern 12 10)) = d2149 pattern
  rw [s1754, s1753]
  rfl
theorem s1756 (pattern : Twelve) : d845 (change pattern 12 10) = d2150 pattern := by
  change (if pattern.f then d831 (change pattern 12 10) else d830 (change pattern 12 10)) = d2150 pattern
  rw [s1755, s1752]
  rfl
theorem s1757 (pattern : Twelve) : d856 (change pattern 12 10) = d2151 pattern := by
  change (if pattern.e then d845 (change pattern 12 10) else d844 (change pattern 12 10)) = d2151 pattern
  rw [s1756, s1751]
  rfl
theorem s1758 (pattern : Twelve) : d862 (change pattern 12 10) = d2152 pattern := by
  change (if pattern.j then d856 (change pattern 12 10) else d855 (change pattern 12 10)) = d2152 pattern
  rw [s1757, s1747]
  rfl
theorem s1759 (pattern : Twelve) : d863 (change pattern 12 10) = d2153 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d854 (change pattern 12 10)) = d2153 pattern
  rw [s1626, s1741]
  rfl
theorem s1760 (pattern : Twelve) : d867 (change pattern 12 10) = d2154 pattern := by
  change (if pattern.d then d863 (change pattern 12 10) else d862 (change pattern 12 10)) = d2154 pattern
  rw [s1759, s1758]
  rfl
theorem s1761 (pattern : Twelve) : d869 (change pattern 12 10) = d2155 pattern := by
  change (if pattern.c then d867 (change pattern 12 10) else d861 (change pattern 12 10)) = d2155 pattern
  rw [s1760, s1742]
  rfl
theorem s1762 (pattern : Twelve) : d8 (change pattern 12 10) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 10) else d1 (change pattern 12 10)) = d8 pattern
  rw [s1619, s1612]
  rfl
theorem s1763 (pattern : Twelve) : d872 (change pattern 12 10) = d8 pattern := by
  change d8 (change pattern 12 10) = d8 pattern
  exact s1762 pattern
theorem s1764 (pattern : Twelve) : d874 (change pattern 12 10) = d2156 pattern := by
  change (if pattern.i then d872 (change pattern 12 10) else d17 (change pattern 12 10)) = d2156 pattern
  rw [s1763, s1615]
  rfl
theorem s1765 (pattern : Twelve) : d875 (change pattern 12 10) = d2157 pattern := by
  change (if pattern.i then d872 (change pattern 12 10) else d814 (change pattern 12 10)) = d2157 pattern
  rw [s1763, s1728]
  rfl
theorem s1766 (pattern : Twelve) : d882 (change pattern 12 10) = d2158 pattern := by
  change (if pattern.h then d875 (change pattern 12 10) else d874 (change pattern 12 10)) = d2158 pattern
  rw [s1765, s1764]
  rfl
theorem s1767 (pattern : Twelve) : d890 (change pattern 12 10) = d2159 pattern := by
  change (if pattern.f then d882 (change pattern 12 10) else d0 (change pattern 12 10)) = d2159 pattern
  rw [s1766, s1611]
  rfl
theorem s1768 (pattern : Twelve) : d876 (change pattern 12 10) = d2160 pattern := by
  change (if pattern.i then d21 (change pattern 12 10) else d19 (change pattern 12 10)) = d2160 pattern
  rw [s1639, s1625]
  rfl
theorem s1769 (pattern : Twelve) : d883 (change pattern 12 10) = d2161 pattern := by
  change (if pattern.h then d42 (change pattern 12 10) else d876 (change pattern 12 10)) = d2161 pattern
  rw [s1679, s1768]
  rfl
theorem s1770 (pattern : Twelve) : d891 (change pattern 12 10) = d2162 pattern := by
  change (if pattern.f then d883 (change pattern 12 10) else d17 (change pattern 12 10)) = d2162 pattern
  rw [s1769, s1615]
  rfl
theorem s1771 (pattern : Twelve) : d898 (change pattern 12 10) = d2163 pattern := by
  change (if pattern.e then d891 (change pattern 12 10) else d890 (change pattern 12 10)) = d2163 pattern
  rw [s1770, s1767]
  rfl
theorem s1772 (pattern : Twelve) : d877 (change pattern 12 10) = d2079 pattern := by
  change (if pattern.i then d815 (change pattern 12 10) else d17 (change pattern 12 10)) = d2079 pattern
  rw [s1748, s1615]
  rfl
theorem s1773 (pattern : Twelve) : d884 (change pattern 12 10) = d2164 pattern := by
  change (if pattern.h then d818 (change pattern 12 10) else d877 (change pattern 12 10)) = d2164 pattern
  rw [s1736, s1772]
  rfl
theorem s1774 (pattern : Twelve) : d892 (change pattern 12 10) = d2165 pattern := by
  change (if pattern.f then d884 (change pattern 12 10) else d56 (change pattern 12 10)) = d2165 pattern
  rw [s1773, s1655]
  rfl
theorem s1775 (pattern : Twelve) : d893 (change pattern 12 10) = d2166 pattern := by
  change (if pattern.f then d883 (change pattern 12 10) else d827 (change pattern 12 10)) = d2166 pattern
  rw [s1769, s1739]
  rfl
theorem s1776 (pattern : Twelve) : d899 (change pattern 12 10) = d2167 pattern := by
  change (if pattern.e then d893 (change pattern 12 10) else d892 (change pattern 12 10)) = d2167 pattern
  rw [s1775, s1774]
  rfl
theorem s1777 (pattern : Twelve) : d902 (change pattern 12 10) = d2168 pattern := by
  change (if pattern.j then d899 (change pattern 12 10) else d898 (change pattern 12 10)) = d2168 pattern
  rw [s1776, s1771]
  rfl
theorem s1778 (pattern : Twelve) : d878 (change pattern 12 10) = d2169 pattern := by
  change (if pattern.i then d24 (change pattern 12 10) else d814 (change pattern 12 10)) = d2169 pattern
  rw [s1675, s1728]
  rfl
theorem s1779 (pattern : Twelve) : d885 (change pattern 12 10) = d2170 pattern := by
  change (if pattern.h then d878 (change pattern 12 10) else d877 (change pattern 12 10)) = d2170 pattern
  rw [s1778, s1772]
  rfl
theorem s1780 (pattern : Twelve) : d894 (change pattern 12 10) = d2171 pattern := by
  change (if pattern.f then d885 (change pattern 12 10) else d30 (change pattern 12 10)) = d2171 pattern
  rw [s1779, s1631]
  rfl
theorem s1781 (pattern : Twelve) : d879 (change pattern 12 10) = d2172 pattern := by
  change (if pattern.i then d119 (change pattern 12 10) else d17 (change pattern 12 10)) = d2172 pattern
  rw [s1711, s1615]
  rfl
theorem s1782 (pattern : Twelve) : d886 (change pattern 12 10) = d2173 pattern := by
  change (if pattern.h then d879 (change pattern 12 10) else d34 (change pattern 12 10)) = d2173 pattern
  rw [s1781, s1647]
  rfl
theorem s1783 (pattern : Twelve) : d895 (change pattern 12 10) = d2174 pattern := by
  change (if pattern.f then d883 (change pattern 12 10) else d886 (change pattern 12 10)) = d2174 pattern
  rw [s1769, s1782]
  rfl
theorem s1784 (pattern : Twelve) : d900 (change pattern 12 10) = d2175 pattern := by
  change (if pattern.e then d895 (change pattern 12 10) else d894 (change pattern 12 10)) = d2175 pattern
  rw [s1783, s1780]
  rfl
theorem s1785 (pattern : Twelve) : d873 (change pattern 12 10) = d15 pattern := by
  change d15 (change pattern 12 10) = d15 pattern
  exact s1674 pattern
theorem s1786 (pattern : Twelve) : d880 (change pattern 12 10) = d2176 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d873 (change pattern 12 10)) = d2176 pattern
  rw [s1626, s1785]
  rfl
theorem s1787 (pattern : Twelve) : d887 (change pattern 12 10) = d2177 pattern := by
  change (if pattern.h then d880 (change pattern 12 10) else d127 (change pattern 12 10)) = d2177 pattern
  rw [s1786, s1718]
  rfl
theorem s1788 (pattern : Twelve) : d896 (change pattern 12 10) = d2178 pattern := by
  change (if pattern.f then d887 (change pattern 12 10) else d59 (change pattern 12 10)) = d2178 pattern
  rw [s1787, s1670]
  rfl
theorem s1789 (pattern : Twelve) : d881 (change pattern 12 10) = d2179 pattern := by
  change (if pattern.i then d118 (change pattern 12 10) else d23 (change pattern 12 10)) = d2179 pattern
  rw [s1708, s1646]
  rfl
theorem s1790 (pattern : Twelve) : d888 (change pattern 12 10) = d2180 pattern := by
  change (if pattern.h then d125 (change pattern 12 10) else d881 (change pattern 12 10)) = d2180 pattern
  rw [s1712, s1789]
  rfl
theorem s1791 (pattern : Twelve) : d889 (change pattern 12 10) = d2181 pattern := by
  change (if pattern.h then d6 (change pattern 12 10) else d42 (change pattern 12 10)) = d2181 pattern
  rw [s1626, s1679]
  rfl
theorem s1792 (pattern : Twelve) : d897 (change pattern 12 10) = d2182 pattern := by
  change (if pattern.f then d889 (change pattern 12 10) else d888 (change pattern 12 10)) = d2182 pattern
  rw [s1791, s1790]
  rfl
theorem s1793 (pattern : Twelve) : d901 (change pattern 12 10) = d2183 pattern := by
  change (if pattern.e then d897 (change pattern 12 10) else d896 (change pattern 12 10)) = d2183 pattern
  rw [s1792, s1788]
  rfl
theorem s1794 (pattern : Twelve) : d903 (change pattern 12 10) = d2184 pattern := by
  change (if pattern.j then d901 (change pattern 12 10) else d900 (change pattern 12 10)) = d2184 pattern
  rw [s1793, s1784]
  rfl
theorem s1795 (pattern : Twelve) : d904 (change pattern 12 10) = d2185 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d899 (change pattern 12 10)) = d2185 pattern
  rw [s1626, s1776]
  rfl
theorem s1796 (pattern : Twelve) : d905 (change pattern 12 10) = d2186 pattern := by
  change (if pattern.d then d904 (change pattern 12 10) else d903 (change pattern 12 10)) = d2186 pattern
  rw [s1795, s1794]
  rfl
theorem s1797 (pattern : Twelve) : d906 (change pattern 12 10) = d2187 pattern := by
  change (if pattern.c then d905 (change pattern 12 10) else d902 (change pattern 12 10)) = d2187 pattern
  rw [s1796, s1777]
  rfl
theorem s1798 (pattern : Twelve) : d907 (change pattern 12 10) = d2188 pattern := by
  change (if pattern.a then d906 (change pattern 12 10) else d869 (change pattern 12 10)) = d2188 pattern
  rw [s1797, s1761]
  rfl
theorem s1799 (pattern : Twelve) : d1275 (change pattern 12 10) = d8 pattern := by
  change d8 (change pattern 12 10) = d8 pattern
  exact s1762 pattern
end NetHack.Sokoban21.Diagram
