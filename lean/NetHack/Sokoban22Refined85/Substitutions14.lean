/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1680 (p : Pattern) : d151 (change p 10000 (some 71)) = d151 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d150 (change p 10000 (some 71))) = d151 p
  rw [sub1531, sub1679]
  rfl
theorem sub1681 (p : Pattern) : d152 (change p 10000 (some 71)) = d152 p := by
  change (if p 160 then d151 (change p 10000 (some 71)) else d114 (change p 10000 (some 71))) = d152 p
  rw [sub1680, sub1641]
  rfl
theorem sub1682 (p : Pattern) : d153 (change p 10000 (some 71)) = d153 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d148 (change p 10000 (some 71))) = d153 p
  rw [sub1531, sub1677]
  rfl
theorem sub1683 (p : Pattern) : d154 (change p 10000 (some 71)) = d154 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d153 (change p 10000 (some 71))) = d154 p
  rw [sub1531, sub1682]
  rfl
theorem sub1684 (p : Pattern) : d155 (change p 10000 (some 71)) = d155 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d154 (change p 10000 (some 71))) = d155 p
  rw [sub1531, sub1683]
  rfl
theorem sub1685 (p : Pattern) : d156 (change p 10000 (some 71)) = d156 p := by
  change (if p 160 then d155 (change p 10000 (some 71)) else d138 (change p 10000 (some 71))) = d156 p
  rw [sub1684, sub1667]
  rfl
theorem sub1686 (p : Pattern) : d157 (change p 10000 (some 71)) = d157 p := by
  change (if p 141 then d156 (change p 10000 (some 71)) else d152 (change p 10000 (some 71))) = d157 p
  rw [sub1685, sub1681]
  rfl
theorem sub1687 (p : Pattern) : d158 (change p 10000 (some 71)) = d158 p := by
  change (if p 138 then d157 (change p 10000 (some 71)) else d147 (change p 10000 (some 71))) = d158 p
  rw [sub1686, sub1676]
  rfl
theorem sub1688 (p : Pattern) : d159 (change p 10000 (some 71)) = d159 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d112 (change p 10000 (some 71))) = d159 p
  rw [sub1531, sub1639]
  rfl
theorem sub1689 (p : Pattern) : d160 (change p 10000 (some 71)) = d160 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d159 (change p 10000 (some 71))) = d160 p
  rw [sub1531, sub1688]
  rfl
theorem sub1690 (p : Pattern) : d161 (change p 10000 (some 71)) = d161 p := by
  change (if p 160 then d12 (change p 10000 (some 71)) else d160 (change p 10000 (some 71))) = d161 p
  rw [sub1531, sub1689]
  rfl
theorem sub1691 (p : Pattern) : d162 (change p 10000 (some 71)) = d162 p := by
  change (if p 141 then d12 (change p 10000 (some 71)) else d161 (change p 10000 (some 71))) = d162 p
  rw [sub1531, sub1690]
  rfl
theorem sub1692 (p : Pattern) : d163 (change p 10000 (some 71)) = d163 p := by
  change (if p 138 then d162 (change p 10000 (some 71)) else d157 (change p 10000 (some 71))) = d163 p
  rw [sub1691, sub1686]
  rfl
theorem sub1693 (p : Pattern) : d164 (change p 10000 (some 71)) = d164 p := by
  change (if p 116 then d163 (change p 10000 (some 71)) else d158 (change p 10000 (some 71))) = d164 p
  rw [sub1692, sub1687]
  rfl
theorem sub1694 (p : Pattern) : d165 (change p 10000 (some 71)) = d165 p := by
  change (if p 138 then d12 (change p 10000 (some 71)) else d157 (change p 10000 (some 71))) = d165 p
  rw [sub1531, sub1686]
  rfl
theorem sub1695 (p : Pattern) : d166 (change p 10000 (some 71)) = d166 p := by
  change (if p 116 then d165 (change p 10000 (some 71)) else d158 (change p 10000 (some 71))) = d166 p
  rw [sub1694, sub1687]
  rfl
theorem sub1696 (p : Pattern) : d167 (change p 10000 (some 71)) = d167 p := by
  change (if p 115 then d166 (change p 10000 (some 71)) else d164 (change p 10000 (some 71))) = d167 p
  rw [sub1695, sub1693]
  rfl
theorem sub1697 (p : Pattern) : d168 (change p 10000 (some 71)) = d167 p := by
  change d167 (change p 10000 (some 71)) = d167 p
  exact sub1696 p
theorem sub1698 (p : Pattern) : d169 (change p 10000 (some 71)) = d4054 p := by
  change (if p 49 then d168 (change p 10000 (some 71)) else d101 (change p 10000 (some 71))) = d4054 p
  rw [sub1697, sub1626]
  rfl
theorem sub1699 (p : Pattern) : d170 (change p 10000 (some 71)) = d170 p := by
  change (if p 182 then d36 (change p 10000 (some 71)) else d31 (change p 10000 (some 71))) = d170 p
  rw [sub1559, sub1553]
  rfl
theorem sub1700 (p : Pattern) : d171 (change p 10000 (some 71)) = d171 p := by
  change (if p 163 then d170 (change p 10000 (some 71)) else d53 (change p 10000 (some 71))) = d171 p
  rw [sub1699, sub1577]
  rfl
theorem sub1701 (p : Pattern) : d172 (change p 10000 (some 71)) = d172 p := by
  change (if p 182 then d41 (change p 10000 (some 71)) else d31 (change p 10000 (some 71))) = d172 p
  rw [sub1565, sub1553]
  rfl
theorem sub1702 (p : Pattern) : d173 (change p 10000 (some 71)) = d173 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d35 (change p 10000 (some 71))) = d173 p
  rw [sub1531, sub1558]
  rfl
theorem sub1703 (p : Pattern) : d174 (change p 10000 (some 71)) = d174 p := by
  change (if p 163 then d173 (change p 10000 (some 71)) else d172 (change p 10000 (some 71))) = d174 p
  rw [sub1702, sub1701]
  rfl
theorem sub1704 (p : Pattern) : d175 (change p 10000 (some 71)) = d175 p := by
  change (if p 162 then d174 (change p 10000 (some 71)) else d171 (change p 10000 (some 71))) = d175 p
  rw [sub1703, sub1700]
  rfl
theorem sub1705 (p : Pattern) : d176 (change p 10000 (some 71)) = d176 p := by
  change (if p 163 then d173 (change p 10000 (some 71)) else d66 (change p 10000 (some 71))) = d176 p
  rw [sub1702, sub1591]
  rfl
theorem sub1706 (p : Pattern) : d177 (change p 10000 (some 71)) = d177 p := by
  change (if p 162 then d73 (change p 10000 (some 71)) else d176 (change p 10000 (some 71))) = d177 p
  rw [sub1598, sub1705]
  rfl
theorem sub1707 (p : Pattern) : d178 (change p 10000 (some 71)) = d178 p := by
  change (if p 161 then d177 (change p 10000 (some 71)) else d175 (change p 10000 (some 71))) = d178 p
  rw [sub1706, sub1704]
  rfl
theorem sub1708 (p : Pattern) : d179 (change p 10000 (some 71)) = d179 p := by
  change (if p 160 then d178 (change p 10000 (some 71)) else d29 (change p 10000 (some 71))) = d179 p
  rw [sub1707, sub1550]
  rfl
theorem sub1709 (p : Pattern) : d180 (change p 10000 (some 71)) = d180 p := by
  change (if p 163 then d43 (change p 10000 (some 71)) else d170 (change p 10000 (some 71))) = d180 p
  rw [sub1567, sub1699]
  rfl
theorem sub1710 (p : Pattern) : d181 (change p 10000 (some 71)) = d181 p := by
  change (if p 163 then d72 (change p 10000 (some 71)) else d173 (change p 10000 (some 71))) = d181 p
  rw [sub1597, sub1702]
  rfl
theorem sub1711 (p : Pattern) : d182 (change p 10000 (some 71)) = d182 p := by
  change (if p 162 then d181 (change p 10000 (some 71)) else d180 (change p 10000 (some 71))) = d182 p
  rw [sub1710, sub1709]
  rfl
theorem sub1712 (p : Pattern) : d183 (change p 10000 (some 71)) = d183 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d173 (change p 10000 (some 71))) = d183 p
  rw [sub1531, sub1702]
  rfl
theorem sub1713 (p : Pattern) : d184 (change p 10000 (some 71)) = d184 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d183 (change p 10000 (some 71))) = d184 p
  rw [sub1531, sub1712]
  rfl
theorem sub1714 (p : Pattern) : d185 (change p 10000 (some 71)) = d185 p := by
  change (if p 161 then d184 (change p 10000 (some 71)) else d182 (change p 10000 (some 71))) = d185 p
  rw [sub1713, sub1711]
  rfl
theorem sub1715 (p : Pattern) : d186 (change p 10000 (some 71)) = d186 p := by
  change (if p 160 then d185 (change p 10000 (some 71)) else d65 (change p 10000 (some 71))) = d186 p
  rw [sub1714, sub1590]
  rfl
theorem sub1716 (p : Pattern) : d187 (change p 10000 (some 71)) = d187 p := by
  change (if p 141 then d186 (change p 10000 (some 71)) else d179 (change p 10000 (some 71))) = d187 p
  rw [sub1715, sub1708]
  rfl
theorem sub1717 (p : Pattern) : d188 (change p 10000 (some 71)) = d188 p := by
  change (if p 162 then d79 (change p 10000 (some 71)) else d16 (change p 10000 (some 71))) = d188 p
  rw [sub1604, sub1535]
  rfl
theorem sub1718 (p : Pattern) : d189 (change p 10000 (some 71)) = d189 p := by
  change (if p 161 then d80 (change p 10000 (some 71)) else d188 (change p 10000 (some 71))) = d189 p
  rw [sub1605, sub1717]
  rfl
theorem sub1719 (p : Pattern) : d8 (change p 10000 (some 71)) = d8 p := by
  rfl
theorem sub1720 (p : Pattern) : d190 (change p 10000 (some 71)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 71)) else d8 (change p 10000 (some 71))) = d190 p
  rw [sub1531, sub1719]
  rfl
theorem sub1721 (p : Pattern) : d191 (change p 10000 (some 71)) = d191 p := by
  change (if p 246 then d190 (change p 10000 (some 71)) else d8 (change p 10000 (some 71))) = d191 p
  rw [sub1720, sub1719]
  rfl
theorem sub1722 (p : Pattern) : d192 (change p 10000 (some 71)) = d192 p := by
  change (if p 204 then d12 (change p 10000 (some 71)) else d191 (change p 10000 (some 71))) = d192 p
  rw [sub1531, sub1721]
  rfl
theorem sub1723 (p : Pattern) : d193 (change p 10000 (some 71)) = d193 p := by
  change (if p 182 then d192 (change p 10000 (some 71)) else d191 (change p 10000 (some 71))) = d193 p
  rw [sub1722, sub1721]
  rfl
theorem sub1724 (p : Pattern) : d194 (change p 10000 (some 71)) = d194 p := by
  change (if p 163 then d193 (change p 10000 (some 71)) else d20 (change p 10000 (some 71))) = d194 p
  rw [sub1723, sub1540]
  rfl
theorem sub1725 (p : Pattern) : d195 (change p 10000 (some 71)) = d195 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d194 (change p 10000 (some 71))) = d195 p
  rw [sub1531, sub1724]
  rfl
theorem sub1726 (p : Pattern) : d196 (change p 10000 (some 71)) = d196 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d195 (change p 10000 (some 71))) = d196 p
  rw [sub1531, sub1725]
  rfl
theorem sub1727 (p : Pattern) : d197 (change p 10000 (some 71)) = d197 p := by
  change (if p 160 then d196 (change p 10000 (some 71)) else d189 (change p 10000 (some 71))) = d197 p
  rw [sub1726, sub1718]
  rfl
theorem sub1728 (p : Pattern) : d198 (change p 10000 (some 71)) = d198 p := by
  change (if p 163 then d62 (change p 10000 (some 71)) else d20 (change p 10000 (some 71))) = d198 p
  rw [sub1587, sub1540]
  rfl
theorem sub1729 (p : Pattern) : d199 (change p 10000 (some 71)) = d199 p := by
  change (if p 162 then d198 (change p 10000 (some 71)) else d53 (change p 10000 (some 71))) = d199 p
  rw [sub1728, sub1577]
  rfl
theorem sub1730 (p : Pattern) : d200 (change p 10000 (some 71)) = d200 p := by
  change (if p 161 then d84 (change p 10000 (some 71)) else d199 (change p 10000 (some 71))) = d200 p
  rw [sub1609, sub1729]
  rfl
theorem sub1731 (p : Pattern) : d201 (change p 10000 (some 71)) = d201 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d193 (change p 10000 (some 71))) = d201 p
  rw [sub1531, sub1723]
  rfl
theorem sub1732 (p : Pattern) : d202 (change p 10000 (some 71)) = d202 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d201 (change p 10000 (some 71))) = d202 p
  rw [sub1531, sub1731]
  rfl
theorem sub1733 (p : Pattern) : d203 (change p 10000 (some 71)) = d203 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d202 (change p 10000 (some 71))) = d203 p
  rw [sub1531, sub1732]
  rfl
theorem sub1734 (p : Pattern) : d204 (change p 10000 (some 71)) = d204 p := by
  change (if p 160 then d203 (change p 10000 (some 71)) else d200 (change p 10000 (some 71))) = d204 p
  rw [sub1733, sub1730]
  rfl
theorem sub1735 (p : Pattern) : d205 (change p 10000 (some 71)) = d205 p := by
  change (if p 141 then d204 (change p 10000 (some 71)) else d197 (change p 10000 (some 71))) = d205 p
  rw [sub1734, sub1727]
  rfl
theorem sub1736 (p : Pattern) : d206 (change p 10000 (some 71)) = d206 p := by
  change (if p 138 then d205 (change p 10000 (some 71)) else d187 (change p 10000 (some 71))) = d206 p
  rw [sub1735, sub1716]
  rfl
theorem sub1737 (p : Pattern) : d207 (change p 10000 (some 71)) = d207 p := by
  change (if p 138 then d12 (change p 10000 (some 71)) else d205 (change p 10000 (some 71))) = d207 p
  rw [sub1531, sub1735]
  rfl
theorem sub1738 (p : Pattern) : d208 (change p 10000 (some 71)) = d208 p := by
  change (if p 116 then d207 (change p 10000 (some 71)) else d206 (change p 10000 (some 71))) = d208 p
  rw [sub1737, sub1736]
  rfl
theorem sub1739 (p : Pattern) : d209 (change p 10000 (some 71)) = d209 p := by
  change (if p 115 then d208 (change p 10000 (some 71)) else d98 (change p 10000 (some 71))) = d209 p
  rw [sub1738, sub1623]
  rfl
theorem sub1740 (p : Pattern) : d210 (change p 10000 (some 71)) = d209 p := by
  change d209 (change p 10000 (some 71)) = d209 p
  exact sub1739 p
theorem sub1741 (p : Pattern) : d211 (change p 10000 (some 71)) = d211 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d109 (change p 10000 (some 71))) = d211 p
  rw [sub1531, sub1636]
  rfl
theorem sub1742 (p : Pattern) : d212 (change p 10000 (some 71)) = d212 p := by
  change (if p 162 then d211 (change p 10000 (some 71)) else d133 (change p 10000 (some 71))) = d212 p
  rw [sub1741, sub1662]
  rfl
theorem sub1743 (p : Pattern) : d213 (change p 10000 (some 71)) = d213 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d211 (change p 10000 (some 71))) = d213 p
  rw [sub1531, sub1741]
  rfl
theorem sub1744 (p : Pattern) : d214 (change p 10000 (some 71)) = d214 p := by
  change (if p 161 then d213 (change p 10000 (some 71)) else d212 (change p 10000 (some 71))) = d214 p
  rw [sub1743, sub1742]
  rfl
theorem sub1745 (p : Pattern) : d215 (change p 10000 (some 71)) = d215 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d125 (change p 10000 (some 71))) = d215 p
  rw [sub1531, sub1654]
  rfl
theorem sub1746 (p : Pattern) : d216 (change p 10000 (some 71)) = d216 p := by
  change (if p 162 then d215 (change p 10000 (some 71)) else d140 (change p 10000 (some 71))) = d216 p
  rw [sub1745, sub1669]
  rfl
theorem sub1747 (p : Pattern) : d217 (change p 10000 (some 71)) = d217 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d215 (change p 10000 (some 71))) = d217 p
  rw [sub1531, sub1745]
  rfl
theorem sub1748 (p : Pattern) : d218 (change p 10000 (some 71)) = d218 p := by
  change (if p 161 then d217 (change p 10000 (some 71)) else d216 (change p 10000 (some 71))) = d218 p
  rw [sub1747, sub1746]
  rfl
theorem sub1749 (p : Pattern) : d219 (change p 10000 (some 71)) = d219 p := by
  change (if p 160 then d218 (change p 10000 (some 71)) else d214 (change p 10000 (some 71))) = d219 p
  rw [sub1748, sub1744]
  rfl
theorem sub1750 (p : Pattern) : d220 (change p 10000 (some 71)) = d220 p := by
  change (if p 141 then d219 (change p 10000 (some 71)) else d131 (change p 10000 (some 71))) = d220 p
  rw [sub1749, sub1660]
  rfl
theorem sub1751 (p : Pattern) : d221 (change p 10000 (some 71)) = d221 p := by
  change (if p 160 then d155 (change p 10000 (some 71)) else d214 (change p 10000 (some 71))) = d221 p
  rw [sub1684, sub1744]
  rfl
theorem sub1752 (p : Pattern) : d222 (change p 10000 (some 71)) = d222 p := by
  change (if p 141 then d221 (change p 10000 (some 71)) else d152 (change p 10000 (some 71))) = d222 p
  rw [sub1751, sub1681]
  rfl
theorem sub1753 (p : Pattern) : d223 (change p 10000 (some 71)) = d223 p := by
  change (if p 138 then d222 (change p 10000 (some 71)) else d220 (change p 10000 (some 71))) = d223 p
  rw [sub1752, sub1750]
  rfl
theorem sub1754 (p : Pattern) : d224 (change p 10000 (some 71)) = d224 p := by
  change (if p 138 then d162 (change p 10000 (some 71)) else d222 (change p 10000 (some 71))) = d224 p
  rw [sub1691, sub1752]
  rfl
theorem sub1755 (p : Pattern) : d225 (change p 10000 (some 71)) = d225 p := by
  change (if p 116 then d224 (change p 10000 (some 71)) else d223 (change p 10000 (some 71))) = d225 p
  rw [sub1754, sub1753]
  rfl
theorem sub1756 (p : Pattern) : d226 (change p 10000 (some 71)) = d226 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d116 (change p 10000 (some 71))) = d226 p
  rw [sub1650, sub1644]
  rfl
theorem sub1757 (p : Pattern) : d227 (change p 10000 (some 71)) = d227 p := by
  change (if p 163 then d226 (change p 10000 (some 71)) else d132 (change p 10000 (some 71))) = d227 p
  rw [sub1756, sub1661]
  rfl
theorem sub1758 (p : Pattern) : d228 (change p 10000 (some 71)) = d228 p := by
  change (if p 162 then d215 (change p 10000 (some 71)) else d227 (change p 10000 (some 71))) = d228 p
  rw [sub1745, sub1757]
  rfl
theorem sub1759 (p : Pattern) : d229 (change p 10000 (some 71)) = d229 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d120 (change p 10000 (some 71))) = d229 p
  rw [sub1531, sub1649]
  rfl
theorem sub1760 (p : Pattern) : d230 (change p 10000 (some 71)) = d230 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d229 (change p 10000 (some 71))) = d230 p
  rw [sub1531, sub1759]
  rfl
theorem sub1761 (p : Pattern) : d231 (change p 10000 (some 71)) = d231 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d230 (change p 10000 (some 71))) = d231 p
  rw [sub1531, sub1760]
  rfl
theorem sub1762 (p : Pattern) : d232 (change p 10000 (some 71)) = d232 p := by
  change (if p 161 then d231 (change p 10000 (some 71)) else d228 (change p 10000 (some 71))) = d232 p
  rw [sub1761, sub1758]
  rfl
theorem sub1763 (p : Pattern) : d233 (change p 10000 (some 71)) = d233 p := by
  change (if p 160 then d232 (change p 10000 (some 71)) else d114 (change p 10000 (some 71))) = d233 p
  rw [sub1762, sub1641]
  rfl
theorem sub1764 (p : Pattern) : d234 (change p 10000 (some 71)) = d234 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d107 (change p 10000 (some 71))) = d234 p
  rw [sub1650, sub1634]
  rfl
theorem sub1765 (p : Pattern) : d235 (change p 10000 (some 71)) = d235 p := by
  change (if p 163 then d125 (change p 10000 (some 71)) else d234 (change p 10000 (some 71))) = d235 p
  rw [sub1654, sub1764]
  rfl
theorem sub1766 (p : Pattern) : d236 (change p 10000 (some 71)) = d236 p := by
  change (if p 162 then d230 (change p 10000 (some 71)) else d235 (change p 10000 (some 71))) = d236 p
  rw [sub1760, sub1765]
  rfl
theorem sub1767 (p : Pattern) : d237 (change p 10000 (some 71)) = d237 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d49 (change p 10000 (some 71))) = d237 p
  rw [sub1531, sub1573]
  rfl
theorem sub1768 (p : Pattern) : d238 (change p 10000 (some 71)) = d238 p := by
  change (if p 161 then d237 (change p 10000 (some 71)) else d236 (change p 10000 (some 71))) = d238 p
  rw [sub1767, sub1766]
  rfl
theorem sub1769 (p : Pattern) : d239 (change p 10000 (some 71)) = d239 p := by
  change (if p 160 then d238 (change p 10000 (some 71)) else d214 (change p 10000 (some 71))) = d239 p
  rw [sub1768, sub1744]
  rfl
theorem sub1770 (p : Pattern) : d240 (change p 10000 (some 71)) = d240 p := by
  change (if p 141 then d239 (change p 10000 (some 71)) else d233 (change p 10000 (some 71))) = d240 p
  rw [sub1769, sub1763]
  rfl
theorem sub1771 (p : Pattern) : d241 (change p 10000 (some 71)) = d241 p := by
  change (if p 163 then d62 (change p 10000 (some 71)) else d132 (change p 10000 (some 71))) = d241 p
  rw [sub1587, sub1661]
  rfl
theorem sub1772 (p : Pattern) : d242 (change p 10000 (some 71)) = d242 p := by
  change (if p 162 then d241 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d242 p
  rw [sub1771, sub1631]
  rfl
theorem sub1773 (p : Pattern) : d243 (change p 10000 (some 71)) = d243 p := by
  change (if p 161 then d137 (change p 10000 (some 71)) else d242 (change p 10000 (some 71))) = d243 p
  rw [sub1666, sub1772]
  rfl
theorem sub1774 (p : Pattern) : d244 (change p 10000 (some 71)) = d244 p := by
  change (if p 160 then d155 (change p 10000 (some 71)) else d243 (change p 10000 (some 71))) = d244 p
  rw [sub1684, sub1773]
  rfl
theorem sub1775 (p : Pattern) : d245 (change p 10000 (some 71)) = d245 p := by
  change (if p 162 then d211 (change p 10000 (some 71)) else d132 (change p 10000 (some 71))) = d245 p
  rw [sub1741, sub1661]
  rfl
theorem sub1776 (p : Pattern) : d246 (change p 10000 (some 71)) = d246 p := by
  change (if p 161 then d154 (change p 10000 (some 71)) else d245 (change p 10000 (some 71))) = d246 p
  rw [sub1683, sub1775]
  rfl
theorem sub1777 (p : Pattern) : d247 (change p 10000 (some 71)) = d247 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d27 (change p 10000 (some 71))) = d247 p
  rw [sub1531, sub1548]
  rfl
theorem sub1778 (p : Pattern) : d248 (change p 10000 (some 71)) = d248 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d247 (change p 10000 (some 71))) = d248 p
  rw [sub1531, sub1777]
  rfl
theorem sub1779 (p : Pattern) : d249 (change p 10000 (some 71)) = d249 p := by
  change (if p 160 then d248 (change p 10000 (some 71)) else d246 (change p 10000 (some 71))) = d249 p
  rw [sub1778, sub1776]
  rfl
theorem sub1780 (p : Pattern) : d250 (change p 10000 (some 71)) = d250 p := by
  change (if p 141 then d249 (change p 10000 (some 71)) else d244 (change p 10000 (some 71))) = d250 p
  rw [sub1779, sub1774]
  rfl
theorem sub1781 (p : Pattern) : d251 (change p 10000 (some 71)) = d251 p := by
  change (if p 138 then d250 (change p 10000 (some 71)) else d240 (change p 10000 (some 71))) = d251 p
  rw [sub1780, sub1770]
  rfl
theorem sub1782 (p : Pattern) : d252 (change p 10000 (some 71)) = d252 p := by
  change (if p 163 then d26 (change p 10000 (some 71)) else d132 (change p 10000 (some 71))) = d252 p
  rw [sub1547, sub1661]
  rfl
theorem sub1783 (p : Pattern) : d253 (change p 10000 (some 71)) = d253 p := by
  change (if p 162 then d252 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d253 p
  rw [sub1782, sub1631]
  rfl
theorem sub1784 (p : Pattern) : d254 (change p 10000 (some 71)) = d254 p := by
  change (if p 163 then d26 (change p 10000 (some 71)) else d109 (change p 10000 (some 71))) = d254 p
  rw [sub1547, sub1636]
  rfl
theorem sub1785 (p : Pattern) : d255 (change p 10000 (some 71)) = d255 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d254 (change p 10000 (some 71))) = d255 p
  rw [sub1531, sub1784]
  rfl
theorem sub1786 (p : Pattern) : d256 (change p 10000 (some 71)) = d256 p := by
  change (if p 161 then d255 (change p 10000 (some 71)) else d253 (change p 10000 (some 71))) = d256 p
  rw [sub1785, sub1783]
  rfl
theorem sub1787 (p : Pattern) : d257 (change p 10000 (some 71)) = d257 p := by
  change (if p 163 then d62 (change p 10000 (some 71)) else d148 (change p 10000 (some 71))) = d257 p
  rw [sub1587, sub1677]
  rfl
theorem sub1788 (p : Pattern) : d258 (change p 10000 (some 71)) = d258 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d257 (change p 10000 (some 71))) = d258 p
  rw [sub1531, sub1787]
  rfl
theorem sub1789 (p : Pattern) : d259 (change p 10000 (some 71)) = d259 p := by
  change (if p 161 then d12 (change p 10000 (some 71)) else d258 (change p 10000 (some 71))) = d259 p
  rw [sub1531, sub1788]
  rfl
theorem sub1790 (p : Pattern) : d260 (change p 10000 (some 71)) = d260 p := by
  change (if p 160 then d259 (change p 10000 (some 71)) else d256 (change p 10000 (some 71))) = d260 p
  rw [sub1789, sub1786]
  rfl
theorem sub1791 (p : Pattern) : d261 (change p 10000 (some 71)) = d261 p := by
  change (if p 141 then d249 (change p 10000 (some 71)) else d260 (change p 10000 (some 71))) = d261 p
  rw [sub1779, sub1790]
  rfl
theorem sub1792 (p : Pattern) : d262 (change p 10000 (some 71)) = d262 p := by
  change (if p 138 then d12 (change p 10000 (some 71)) else d261 (change p 10000 (some 71))) = d262 p
  rw [sub1531, sub1791]
  rfl
theorem sub1793 (p : Pattern) : d263 (change p 10000 (some 71)) = d263 p := by
  change (if p 116 then d262 (change p 10000 (some 71)) else d251 (change p 10000 (some 71))) = d263 p
  rw [sub1792, sub1781]
  rfl
theorem sub1794 (p : Pattern) : d264 (change p 10000 (some 71)) = d264 p := by
  change (if p 115 then d263 (change p 10000 (some 71)) else d225 (change p 10000 (some 71))) = d264 p
  rw [sub1793, sub1755]
  rfl
theorem sub1795 (p : Pattern) : d265 (change p 10000 (some 71)) = d264 p := by
  change d264 (change p 10000 (some 71)) = d264 p
  exact sub1794 p
theorem sub1796 (p : Pattern) : d266 (change p 10000 (some 71)) = d4055 p := by
  change (if p 49 then d265 (change p 10000 (some 71)) else d210 (change p 10000 (some 71))) = d4055 p
  rw [sub1795, sub1740]
  rfl
theorem sub1797 (p : Pattern) : d267 (change p 10000 (some 71)) = d4056 p := by
  change (if p 48 then d266 (change p 10000 (some 71)) else d169 (change p 10000 (some 71))) = d4056 p
  rw [sub1796, sub1698]
  rfl
theorem sub1798 (p : Pattern) : d0 (change p 10000 (some 115)) = d0 p := by
  rfl
theorem sub1799 (p : Pattern) : d12 (change p 10000 (some 115)) = d12 p := by
  rfl
end NetHack.Sokoban22Refined85
