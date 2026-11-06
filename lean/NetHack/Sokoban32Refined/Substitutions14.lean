/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1680 (p : Pattern) : d321 (change p 133 (some 134)) = d1153 p := by
  change (if p 106 then d320 (change p 133 (some 134)) else d301 (change p 133 (some 134))) = d1153 p
  rw [sub1679, sub1657]
  simp only [ite_self]
theorem sub1681 (p : Pattern) : d322 (change p 133 (some 134)) = d1160 p := by
  change (if p 113 then d295 (change p 133 (some 134)) else d318 (change p 133 (some 134))) = d1160 p
  rw [sub1651, sub1677]
  rfl
theorem sub1682 (p : Pattern) : d323 (change p 133 (some 134)) = d1161 p := by
  change (if p 113 then d2 (change p 133 (some 134)) else d312 (change p 133 (some 134))) = d1161 p
  rw [sub1631, sub1671]
  rfl
theorem sub1683 (p : Pattern) : d324 (change p 133 (some 134)) = d1162 p := by
  change (if p 112 then d323 (change p 133 (some 134)) else d322 (change p 133 (some 134))) = d1162 p
  rw [sub1682, sub1681]
  rfl
theorem sub1684 (p : Pattern) : d325 (change p 133 (some 134)) = d1163 p := by
  change (if p 106 then d324 (change p 133 (some 134)) else d314 (change p 133 (some 134))) = d1163 p
  rw [sub1683, sub1673]
  rfl
theorem sub1685 (p : Pattern) : d326 (change p 133 (some 134)) = d1164 p := by
  change (if p 86 then d325 (change p 133 (some 134)) else d321 (change p 133 (some 134))) = d1164 p
  rw [sub1684, sub1680]
  rfl
theorem sub1686 (p : Pattern) : d327 (change p 133 (some 134)) = d1165 p := by
  change (if p 80 then d326 (change p 133 (some 134)) else d316 (change p 133 (some 134))) = d1165 p
  rw [sub1685, sub1675]
  rfl
theorem sub1687 (p : Pattern) : d0 (change p 134 none) = d0 p := by
  rfl
theorem sub1688 (p : Pattern) : d2 (change p 134 none) = d2 p := by
  rfl
theorem sub1689 (p : Pattern) : d3 (change p 134 none) = d3 p := by
  change (if p 161 then d2 (change p 134 none) else d0 (change p 134 none)) = d3 p
  rw [sub1688, sub1687]
  rfl
theorem sub1690 (p : Pattern) : d4 (change p 134 none) = d4 p := by
  change (if p 160 then d3 (change p 134 none) else d0 (change p 134 none)) = d4 p
  rw [sub1689, sub1687]
  rfl
theorem sub1691 (p : Pattern) : d5 (change p 134 none) = d5 p := by
  change (if p 160 then d2 (change p 134 none) else d0 (change p 134 none)) = d5 p
  rw [sub1688, sub1687]
  rfl
theorem sub1692 (p : Pattern) : d6 (change p 134 none) = d6 p := by
  change (if p 159 then d5 (change p 134 none) else d4 (change p 134 none)) = d6 p
  rw [sub1691, sub1690]
  rfl
theorem sub1693 (p : Pattern) : d7 (change p 134 none) = d7 p := by
  change (if p 159 then d2 (change p 134 none) else d4 (change p 134 none)) = d7 p
  rw [sub1688, sub1690]
  rfl
theorem sub1694 (p : Pattern) : d8 (change p 134 none) = d8 p := by
  change (if p 158 then d7 (change p 134 none) else d6 (change p 134 none)) = d8 p
  rw [sub1693, sub1692]
  rfl
theorem sub1695 (p : Pattern) : d1 (change p 134 none) = d1 p := by
  rfl
theorem sub1696 (p : Pattern) : d9 (change p 134 none) = d9 p := by
  change (if p 161 then d2 (change p 134 none) else d1 (change p 134 none)) = d9 p
  rw [sub1688, sub1695]
  rfl
theorem sub1697 (p : Pattern) : d10 (change p 134 none) = d10 p := by
  change (if p 160 then d9 (change p 134 none) else d1 (change p 134 none)) = d10 p
  rw [sub1696, sub1695]
  rfl
theorem sub1698 (p : Pattern) : d11 (change p 134 none) = d11 p := by
  change (if p 160 then d2 (change p 134 none) else d1 (change p 134 none)) = d11 p
  rw [sub1688, sub1695]
  rfl
theorem sub1699 (p : Pattern) : d12 (change p 134 none) = d12 p := by
  change (if p 159 then d11 (change p 134 none) else d10 (change p 134 none)) = d12 p
  rw [sub1698, sub1697]
  rfl
theorem sub1700 (p : Pattern) : d13 (change p 134 none) = d13 p := by
  change (if p 159 then d2 (change p 134 none) else d10 (change p 134 none)) = d13 p
  rw [sub1688, sub1697]
  rfl
theorem sub1701 (p : Pattern) : d14 (change p 134 none) = d14 p := by
  change (if p 158 then d13 (change p 134 none) else d12 (change p 134 none)) = d14 p
  rw [sub1700, sub1699]
  rfl
theorem sub1702 (p : Pattern) : d15 (change p 134 none) = d15 p := by
  change (if p 139 then d14 (change p 134 none) else d8 (change p 134 none)) = d15 p
  rw [sub1701, sub1694]
  rfl
theorem sub1703 (p : Pattern) : d16 (change p 134 none) = d16 p := by
  change (if p 138 then d15 (change p 134 none) else d8 (change p 134 none)) = d16 p
  rw [sub1702, sub1694]
  rfl
theorem sub1704 (p : Pattern) : d328 (change p 134 none) = d16 p := by
  change d16 (change p 134 none) = d16 p
  exact sub1703 p
theorem sub1705 (p : Pattern) : d37 (change p 134 none) = d37 p := by
  change (if p 159 then d2 (change p 134 none) else d5 (change p 134 none)) = d37 p
  rw [sub1688, sub1691]
  rfl
theorem sub1706 (p : Pattern) : d38 (change p 134 none) = d38 p := by
  change (if p 158 then d37 (change p 134 none) else d6 (change p 134 none)) = d38 p
  rw [sub1705, sub1692]
  rfl
theorem sub1707 (p : Pattern) : d39 (change p 134 none) = d39 p := by
  change (if p 159 then d2 (change p 134 none) else d11 (change p 134 none)) = d39 p
  rw [sub1688, sub1698]
  rfl
theorem sub1708 (p : Pattern) : d40 (change p 134 none) = d40 p := by
  change (if p 158 then d39 (change p 134 none) else d12 (change p 134 none)) = d40 p
  rw [sub1707, sub1699]
  rfl
theorem sub1709 (p : Pattern) : d41 (change p 134 none) = d41 p := by
  change (if p 139 then d40 (change p 134 none) else d38 (change p 134 none)) = d41 p
  rw [sub1708, sub1706]
  rfl
theorem sub1710 (p : Pattern) : d42 (change p 134 none) = d42 p := by
  change (if p 138 then d41 (change p 134 none) else d38 (change p 134 none)) = d42 p
  rw [sub1709, sub1706]
  rfl
theorem sub1711 (p : Pattern) : d329 (change p 134 none) = d42 p := by
  change d42 (change p 134 none) = d42 p
  exact sub1710 p
theorem sub1712 (p : Pattern) : d330 (change p 134 none) = d1176 p := by
  change (if p 133 then d329 (change p 134 none) else d328 (change p 134 none)) = d1176 p
  rw [sub1711, sub1704]
  rfl
theorem sub1713 (p : Pattern) : d331 (change p 134 none) = d1177 p := by
  change (if p 132 then d330 (change p 134 none) else d328 (change p 134 none)) = d1177 p
  rw [sub1712, sub1704]
  rfl
theorem sub1714 (p : Pattern) : d332 (change p 134 none) = d15 p := by
  change d15 (change p 134 none) = d15 p
  exact sub1702 p
theorem sub1715 (p : Pattern) : d333 (change p 134 none) = d41 p := by
  change d41 (change p 134 none) = d41 p
  exact sub1709 p
theorem sub1716 (p : Pattern) : d334 (change p 134 none) = d1178 p := by
  change (if p 133 then d333 (change p 134 none) else d332 (change p 134 none)) = d1178 p
  rw [sub1715, sub1714]
  rfl
theorem sub1717 (p : Pattern) : d335 (change p 134 none) = d1179 p := by
  change (if p 132 then d334 (change p 134 none) else d332 (change p 134 none)) = d1179 p
  rw [sub1716, sub1714]
  rfl
theorem sub1718 (p : Pattern) : d52 (change p 134 none) = d52 p := by
  change (if p 139 then d2 (change p 134 none) else d8 (change p 134 none)) = d52 p
  rw [sub1688, sub1694]
  rfl
theorem sub1719 (p : Pattern) : d53 (change p 134 none) = d53 p := by
  change (if p 138 then d52 (change p 134 none) else d15 (change p 134 none)) = d53 p
  rw [sub1718, sub1702]
  rfl
theorem sub1720 (p : Pattern) : d336 (change p 134 none) = d53 p := by
  change d53 (change p 134 none) = d53 p
  exact sub1719 p
theorem sub1721 (p : Pattern) : d61 (change p 134 none) = d61 p := by
  change (if p 139 then d2 (change p 134 none) else d38 (change p 134 none)) = d61 p
  rw [sub1688, sub1706]
  rfl
theorem sub1722 (p : Pattern) : d62 (change p 134 none) = d62 p := by
  change (if p 138 then d61 (change p 134 none) else d41 (change p 134 none)) = d62 p
  rw [sub1721, sub1709]
  rfl
theorem sub1723 (p : Pattern) : d337 (change p 134 none) = d62 p := by
  change d62 (change p 134 none) = d62 p
  exact sub1722 p
theorem sub1724 (p : Pattern) : d338 (change p 134 none) = d1180 p := by
  change (if p 133 then d337 (change p 134 none) else d336 (change p 134 none)) = d1180 p
  rw [sub1723, sub1720]
  rfl
theorem sub1725 (p : Pattern) : d339 (change p 134 none) = d1181 p := by
  change (if p 132 then d338 (change p 134 none) else d336 (change p 134 none)) = d1181 p
  rw [sub1724, sub1720]
  rfl
theorem sub1726 (p : Pattern) : d340 (change p 134 none) = d1182 p := by
  change (if p 113 then d339 (change p 134 none) else d335 (change p 134 none)) = d1182 p
  rw [sub1725, sub1717]
  rfl
theorem sub1727 (p : Pattern) : d341 (change p 134 none) = d1183 p := by
  change (if p 112 then d340 (change p 134 none) else d331 (change p 134 none)) = d1183 p
  rw [sub1726, sub1713]
  rfl
theorem sub1728 (p : Pattern) : d68 (change p 134 none) = d68 p := by
  change (if p 139 then d2 (change p 134 none) else d40 (change p 134 none)) = d68 p
  rw [sub1688, sub1708]
  rfl
theorem sub1729 (p : Pattern) : d69 (change p 134 none) = d69 p := by
  change (if p 138 then d68 (change p 134 none) else d40 (change p 134 none)) = d69 p
  rw [sub1728, sub1708]
  rfl
theorem sub1730 (p : Pattern) : d342 (change p 134 none) = d69 p := by
  change d69 (change p 134 none) = d69 p
  exact sub1729 p
theorem sub1731 (p : Pattern) : d343 (change p 134 none) = d1184 p := by
  change (if p 133 then d342 (change p 134 none) else d328 (change p 134 none)) = d1184 p
  rw [sub1730, sub1704]
  rfl
theorem sub1732 (p : Pattern) : d344 (change p 134 none) = d1185 p := by
  change (if p 132 then d343 (change p 134 none) else d328 (change p 134 none)) = d1185 p
  rw [sub1731, sub1704]
  rfl
theorem sub1733 (p : Pattern) : d345 (change p 134 none) = d68 p := by
  change d68 (change p 134 none) = d68 p
  exact sub1728 p
theorem sub1734 (p : Pattern) : d346 (change p 134 none) = d1186 p := by
  change (if p 133 then d345 (change p 134 none) else d328 (change p 134 none)) = d1186 p
  rw [sub1733, sub1704]
  rfl
theorem sub1735 (p : Pattern) : d347 (change p 134 none) = d1187 p := by
  change (if p 132 then d346 (change p 134 none) else d328 (change p 134 none)) = d1187 p
  rw [sub1734, sub1704]
  rfl
theorem sub1736 (p : Pattern) : d348 (change p 134 none) = d1188 p := by
  change (if p 113 then d347 (change p 134 none) else d344 (change p 134 none)) = d1188 p
  rw [sub1735, sub1732]
  rfl
theorem sub1737 (p : Pattern) : d349 (change p 134 none) = d1189 p := by
  change (if p 133 then d345 (change p 134 none) else d332 (change p 134 none)) = d1189 p
  rw [sub1733, sub1714]
  rfl
theorem sub1738 (p : Pattern) : d350 (change p 134 none) = d1190 p := by
  change (if p 132 then d349 (change p 134 none) else d332 (change p 134 none)) = d1190 p
  rw [sub1737, sub1714]
  rfl
theorem sub1739 (p : Pattern) : d351 (change p 134 none) = d1191 p := by
  change (if p 133 then d345 (change p 134 none) else d336 (change p 134 none)) = d1191 p
  rw [sub1733, sub1720]
  rfl
theorem sub1740 (p : Pattern) : d352 (change p 134 none) = d1192 p := by
  change (if p 132 then d351 (change p 134 none) else d336 (change p 134 none)) = d1192 p
  rw [sub1739, sub1720]
  rfl
theorem sub1741 (p : Pattern) : d353 (change p 134 none) = d1193 p := by
  change (if p 113 then d352 (change p 134 none) else d350 (change p 134 none)) = d1193 p
  rw [sub1740, sub1738]
  rfl
theorem sub1742 (p : Pattern) : d354 (change p 134 none) = d1194 p := by
  change (if p 112 then d353 (change p 134 none) else d348 (change p 134 none)) = d1194 p
  rw [sub1741, sub1736]
  rfl
theorem sub1743 (p : Pattern) : d355 (change p 134 none) = d1195 p := by
  change (if p 106 then d354 (change p 134 none) else d341 (change p 134 none)) = d1195 p
  rw [sub1742, sub1727]
  rfl
theorem sub1744 (p : Pattern) : d86 (change p 134 none) = d86 p := by
  change (if p 138 then d52 (change p 134 none) else d8 (change p 134 none)) = d86 p
  rw [sub1718, sub1694]
  rfl
theorem sub1745 (p : Pattern) : d356 (change p 134 none) = d86 p := by
  change d86 (change p 134 none) = d86 p
  exact sub1744 p
theorem sub1746 (p : Pattern) : d92 (change p 134 none) = d92 p := by
  change (if p 138 then d61 (change p 134 none) else d38 (change p 134 none)) = d92 p
  rw [sub1721, sub1706]
  rfl
theorem sub1747 (p : Pattern) : d357 (change p 134 none) = d92 p := by
  change d92 (change p 134 none) = d92 p
  exact sub1746 p
theorem sub1748 (p : Pattern) : d358 (change p 134 none) = d1196 p := by
  change (if p 133 then d357 (change p 134 none) else d356 (change p 134 none)) = d1196 p
  rw [sub1747, sub1745]
  rfl
theorem sub1749 (p : Pattern) : d359 (change p 134 none) = d1197 p := by
  change (if p 132 then d358 (change p 134 none) else d356 (change p 134 none)) = d1197 p
  rw [sub1748, sub1745]
  rfl
theorem sub1750 (p : Pattern) : d360 (change p 134 none) = d1198 p := by
  change (if p 113 then d359 (change p 134 none) else d331 (change p 134 none)) = d1198 p
  rw [sub1749, sub1713]
  rfl
theorem sub1751 (p : Pattern) : d97 (change p 134 none) = d97 p := by
  change (if p 139 then d2 (change p 134 none) else d14 (change p 134 none)) = d97 p
  rw [sub1688, sub1701]
  rfl
theorem sub1752 (p : Pattern) : d98 (change p 134 none) = d98 p := by
  change (if p 138 then d97 (change p 134 none) else d14 (change p 134 none)) = d98 p
  rw [sub1751, sub1701]
  rfl
theorem sub1753 (p : Pattern) : d361 (change p 134 none) = d98 p := by
  change d98 (change p 134 none) = d98 p
  exact sub1752 p
theorem sub1754 (p : Pattern) : d362 (change p 134 none) = d1199 p := by
  change (if p 133 then d342 (change p 134 none) else d361 (change p 134 none)) = d1199 p
  rw [sub1730, sub1753]
  rfl
theorem sub1755 (p : Pattern) : d363 (change p 134 none) = d1200 p := by
  change (if p 132 then d362 (change p 134 none) else d361 (change p 134 none)) = d1200 p
  rw [sub1754, sub1753]
  rfl
theorem sub1756 (p : Pattern) : d364 (change p 134 none) = d1201 p := by
  change (if p 112 then d363 (change p 134 none) else d360 (change p 134 none)) = d1201 p
  rw [sub1755, sub1750]
  rfl
theorem sub1757 (p : Pattern) : d365 (change p 134 none) = d1202 p := by
  change (if p 133 then d345 (change p 134 none) else d356 (change p 134 none)) = d1202 p
  rw [sub1733, sub1745]
  rfl
theorem sub1758 (p : Pattern) : d366 (change p 134 none) = d1203 p := by
  change (if p 132 then d365 (change p 134 none) else d356 (change p 134 none)) = d1203 p
  rw [sub1757, sub1745]
  rfl
theorem sub1759 (p : Pattern) : d367 (change p 134 none) = d1204 p := by
  change (if p 113 then d366 (change p 134 none) else d347 (change p 134 none)) = d1204 p
  rw [sub1758, sub1735]
  rfl
theorem sub1760 (p : Pattern) : d368 (change p 134 none) = d307 p := by
  change (if p 133 then d2 (change p 134 none) else d361 (change p 134 none)) = d307 p
  rw [sub1688, sub1753]
  rfl
theorem sub1761 (p : Pattern) : d369 (change p 134 none) = d1205 p := by
  change (if p 132 then d368 (change p 134 none) else d361 (change p 134 none)) = d1205 p
  rw [sub1760, sub1753]
  rfl
theorem sub1762 (p : Pattern) : d370 (change p 134 none) = d97 p := by
  change d97 (change p 134 none) = d97 p
  exact sub1751 p
theorem sub1763 (p : Pattern) : d371 (change p 134 none) = d312 p := by
  change (if p 133 then d2 (change p 134 none) else d370 (change p 134 none)) = d312 p
  rw [sub1688, sub1762]
  rfl
theorem sub1764 (p : Pattern) : d372 (change p 134 none) = d1206 p := by
  change (if p 132 then d371 (change p 134 none) else d370 (change p 134 none)) = d1206 p
  rw [sub1763, sub1762]
  rfl
theorem sub1765 (p : Pattern) : d373 (change p 134 none) = d1207 p := by
  change (if p 113 then d372 (change p 134 none) else d369 (change p 134 none)) = d1207 p
  rw [sub1764, sub1761]
  rfl
theorem sub1766 (p : Pattern) : d374 (change p 134 none) = d1208 p := by
  change (if p 112 then d373 (change p 134 none) else d367 (change p 134 none)) = d1208 p
  rw [sub1765, sub1759]
  rfl
theorem sub1767 (p : Pattern) : d375 (change p 134 none) = d1209 p := by
  change (if p 106 then d374 (change p 134 none) else d364 (change p 134 none)) = d1209 p
  rw [sub1766, sub1756]
  rfl
theorem sub1768 (p : Pattern) : d376 (change p 134 none) = d1210 p := by
  change (if p 86 then d375 (change p 134 none) else d355 (change p 134 none)) = d1210 p
  rw [sub1767, sub1743]
  rfl
theorem sub1769 (p : Pattern) : d377 (change p 134 none) = d1211 p := by
  change (if p 112 then d353 (change p 134 none) else d347 (change p 134 none)) = d1211 p
  rw [sub1741, sub1735]
  rfl
theorem sub1770 (p : Pattern) : d378 (change p 134 none) = d1212 p := by
  change (if p 106 then d377 (change p 134 none) else d341 (change p 134 none)) = d1212 p
  rw [sub1769, sub1727]
  rfl
theorem sub1771 (p : Pattern) : d379 (change p 134 none) = d1213 p := by
  change (if p 133 then d345 (change p 134 none) else d370 (change p 134 none)) = d1213 p
  rw [sub1733, sub1762]
  rfl
theorem sub1772 (p : Pattern) : d380 (change p 134 none) = d1214 p := by
  change (if p 132 then d379 (change p 134 none) else d370 (change p 134 none)) = d1214 p
  rw [sub1771, sub1762]
  rfl
theorem sub1773 (p : Pattern) : d381 (change p 134 none) = d1215 p := by
  change (if p 113 then d380 (change p 134 none) else d363 (change p 134 none)) = d1215 p
  rw [sub1772, sub1755]
  rfl
theorem sub1774 (p : Pattern) : d382 (change p 134 none) = d1216 p := by
  change (if p 112 then d381 (change p 134 none) else d360 (change p 134 none)) = d1216 p
  rw [sub1773, sub1750]
  rfl
theorem sub1775 (p : Pattern) : d383 (change p 134 none) = d1217 p := by
  change (if p 113 then d352 (change p 134 none) else d347 (change p 134 none)) = d1217 p
  rw [sub1740, sub1735]
  rfl
theorem sub1776 (p : Pattern) : d384 (change p 134 none) = d1218 p := by
  change (if p 113 then d2 (change p 134 none) else d372 (change p 134 none)) = d1218 p
  rw [sub1688, sub1764]
  rfl
theorem sub1777 (p : Pattern) : d385 (change p 134 none) = d1219 p := by
  change (if p 112 then d384 (change p 134 none) else d383 (change p 134 none)) = d1219 p
  rw [sub1776, sub1775]
  rfl
theorem sub1778 (p : Pattern) : d386 (change p 134 none) = d1220 p := by
  change (if p 106 then d385 (change p 134 none) else d382 (change p 134 none)) = d1220 p
  rw [sub1777, sub1774]
  rfl
theorem sub1779 (p : Pattern) : d387 (change p 134 none) = d1221 p := by
  change (if p 86 then d386 (change p 134 none) else d378 (change p 134 none)) = d1221 p
  rw [sub1778, sub1770]
  rfl
theorem sub1780 (p : Pattern) : d388 (change p 134 none) = d1222 p := by
  change (if p 80 then d387 (change p 134 none) else d376 (change p 134 none)) = d1222 p
  rw [sub1779, sub1768]
  rfl
theorem sub1781 (p : Pattern) : d0 (change p 132 none) = d0 p := by
  rfl
theorem sub1782 (p : Pattern) : d2 (change p 132 none) = d2 p := by
  rfl
theorem sub1783 (p : Pattern) : d3 (change p 132 none) = d3 p := by
  change (if p 161 then d2 (change p 132 none) else d0 (change p 132 none)) = d3 p
  rw [sub1782, sub1781]
  rfl
theorem sub1784 (p : Pattern) : d4 (change p 132 none) = d4 p := by
  change (if p 160 then d3 (change p 132 none) else d0 (change p 132 none)) = d4 p
  rw [sub1783, sub1781]
  rfl
theorem sub1785 (p : Pattern) : d5 (change p 132 none) = d5 p := by
  change (if p 160 then d2 (change p 132 none) else d0 (change p 132 none)) = d5 p
  rw [sub1782, sub1781]
  rfl
theorem sub1786 (p : Pattern) : d6 (change p 132 none) = d6 p := by
  change (if p 159 then d5 (change p 132 none) else d4 (change p 132 none)) = d6 p
  rw [sub1785, sub1784]
  rfl
theorem sub1787 (p : Pattern) : d7 (change p 132 none) = d7 p := by
  change (if p 159 then d2 (change p 132 none) else d4 (change p 132 none)) = d7 p
  rw [sub1782, sub1784]
  rfl
theorem sub1788 (p : Pattern) : d8 (change p 132 none) = d8 p := by
  change (if p 158 then d7 (change p 132 none) else d6 (change p 132 none)) = d8 p
  rw [sub1787, sub1786]
  rfl
theorem sub1789 (p : Pattern) : d1 (change p 132 none) = d1 p := by
  rfl
theorem sub1790 (p : Pattern) : d9 (change p 132 none) = d9 p := by
  change (if p 161 then d2 (change p 132 none) else d1 (change p 132 none)) = d9 p
  rw [sub1782, sub1789]
  rfl
theorem sub1791 (p : Pattern) : d10 (change p 132 none) = d10 p := by
  change (if p 160 then d9 (change p 132 none) else d1 (change p 132 none)) = d10 p
  rw [sub1790, sub1789]
  rfl
theorem sub1792 (p : Pattern) : d11 (change p 132 none) = d11 p := by
  change (if p 160 then d2 (change p 132 none) else d1 (change p 132 none)) = d11 p
  rw [sub1782, sub1789]
  rfl
theorem sub1793 (p : Pattern) : d12 (change p 132 none) = d12 p := by
  change (if p 159 then d11 (change p 132 none) else d10 (change p 132 none)) = d12 p
  rw [sub1792, sub1791]
  rfl
theorem sub1794 (p : Pattern) : d13 (change p 132 none) = d13 p := by
  change (if p 159 then d2 (change p 132 none) else d10 (change p 132 none)) = d13 p
  rw [sub1782, sub1791]
  rfl
theorem sub1795 (p : Pattern) : d14 (change p 132 none) = d14 p := by
  change (if p 158 then d13 (change p 132 none) else d12 (change p 132 none)) = d14 p
  rw [sub1794, sub1793]
  rfl
theorem sub1796 (p : Pattern) : d15 (change p 132 none) = d15 p := by
  change (if p 139 then d14 (change p 132 none) else d8 (change p 132 none)) = d15 p
  rw [sub1795, sub1788]
  rfl
theorem sub1797 (p : Pattern) : d16 (change p 132 none) = d16 p := by
  change (if p 138 then d15 (change p 132 none) else d8 (change p 132 none)) = d16 p
  rw [sub1796, sub1788]
  rfl
theorem sub1798 (p : Pattern) : d17 (change p 132 none) = d17 p := by
  change (if p 160 then d2 (change p 132 none) else d3 (change p 132 none)) = d17 p
  rw [sub1782, sub1783]
  rfl
theorem sub1799 (p : Pattern) : d18 (change p 132 none) = d18 p := by
  change (if p 159 then d17 (change p 132 none) else d4 (change p 132 none)) = d18 p
  rw [sub1798, sub1784]
  rfl
end NetHack.Sokoban32Refined
