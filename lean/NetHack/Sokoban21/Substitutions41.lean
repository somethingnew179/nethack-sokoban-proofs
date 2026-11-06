/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions40
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s6150 (pattern : Twelve) : d1653 (change pattern 12 6) = d1653 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d821 (change pattern 12 6)) = d1653 pattern
  rw [s5921, s6038]
  rfl
theorem s6151 (pattern : Twelve) : d1658 (change pattern 12 6) = d1658 pattern := by
  change (if pattern.e then d1653 (change pattern 12 6) else d1652 (change pattern 12 6)) = d1658 pattern
  rw [s6150, s6149]
  rfl
theorem s6152 (pattern : Twelve) : d1646 (change pattern 12 6) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 12 6) else d20 (change pattern 12 6)) = d1646 pattern
  rw [s5938, s5930]
  rfl
theorem s6153 (pattern : Twelve) : d128 (change pattern 12 6) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d20 (change pattern 12 6)) = d128 pattern
  rw [s5921, s5930]
  rfl
theorem s6154 (pattern : Twelve) : d1648 (change pattern 12 6) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 12 6) else d1646 (change pattern 12 6)) = d1648 pattern
  rw [s6153, s6152]
  rfl
theorem s6155 (pattern : Twelve) : d1654 (change pattern 12 6) = d1654 pattern := by
  change (if pattern.f then d1648 (change pattern 12 6) else d1289 (change pattern 12 6)) = d1654 pattern
  rw [s6154, s6145]
  rfl
theorem s6156 (pattern : Twelve) : d1655 (change pattern 12 6) = d1655 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d822 (change pattern 12 6)) = d1655 pattern
  rw [s5921, s6039]
  rfl
theorem s6157 (pattern : Twelve) : d1659 (change pattern 12 6) = d1659 pattern := by
  change (if pattern.e then d1655 (change pattern 12 6) else d1654 (change pattern 12 6)) = d1659 pattern
  rw [s6156, s6155]
  rfl
theorem s6158 (pattern : Twelve) : d1661 (change pattern 12 6) = d1661 pattern := by
  change (if pattern.j then d1659 (change pattern 12 6) else d1658 (change pattern 12 6)) = d1661 pattern
  rw [s6157, s6151]
  rfl
theorem s6159 (pattern : Twelve) : d1662 (change pattern 12 6) = d1662 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d1657 (change pattern 12 6)) = d1662 pattern
  rw [s5921, s6147]
  rfl
theorem s6160 (pattern : Twelve) : d1663 (change pattern 12 6) = d1663 pattern := by
  change (if pattern.d then d1662 (change pattern 12 6) else d1661 (change pattern 12 6)) = d1663 pattern
  rw [s6159, s6158]
  rfl
theorem s6161 (pattern : Twelve) : d1664 (change pattern 12 6) = d1664 pattern := by
  change (if pattern.c then d1663 (change pattern 12 6) else d1660 (change pattern 12 6)) = d1664 pattern
  rw [s6160, s6148]
  rfl
theorem s6162 (pattern : Twelve) : d1814 (change pattern 12 6) = d1814 pattern := by
  change (if pattern.f then d20 (change pattern 12 6) else d25 (change pattern 12 6)) = d1814 pattern
  rw [s5930, s5987]
  rfl
theorem s6163 (pattern : Twelve) : d1815 (change pattern 12 6) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 12 6) else d21 (change pattern 12 6)) = d1815 pattern
  rw [s5921, s5934]
  rfl
theorem s6164 (pattern : Twelve) : d1818 (change pattern 12 6) = d1818 pattern := by
  change (if pattern.e then d1815 (change pattern 12 6) else d1814 (change pattern 12 6)) = d1818 pattern
  rw [s6163, s6162]
  rfl
theorem s6165 (pattern : Twelve) : d1821 (change pattern 12 6) = d1821 pattern := by
  change (if pattern.j then d1659 (change pattern 12 6) else d1818 (change pattern 12 6)) = d1821 pattern
  rw [s6157, s6164]
  rfl
theorem s6166 (pattern : Twelve) : d1816 (change pattern 12 6) = d1816 pattern := by
  change (if pattern.f then d1646 (change pattern 12 6) else d821 (change pattern 12 6)) = d1816 pattern
  rw [s6152, s6038]
  rfl
theorem s6167 (pattern : Twelve) : d1819 (change pattern 12 6) = d1819 pattern := by
  change (if pattern.e then d1655 (change pattern 12 6) else d1816 (change pattern 12 6)) = d1819 pattern
  rw [s6156, s6166]
  rfl
theorem s6168 (pattern : Twelve) : d183 (change pattern 12 6) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 12 6) else d22 (change pattern 12 6)) = d183 pattern
  rw [s5921, s5938]
  rfl
theorem s6169 (pattern : Twelve) : d1817 (change pattern 12 6) = d1817 pattern := by
  change (if pattern.f then d183 (change pattern 12 6) else d822 (change pattern 12 6)) = d1817 pattern
  rw [s6168, s6039]
  rfl
theorem s6170 (pattern : Twelve) : d1820 (change pattern 12 6) = d1820 pattern := by
  change (if pattern.e then d6 (change pattern 12 6) else d1817 (change pattern 12 6)) = d1820 pattern
  rw [s5921, s6169]
  rfl
theorem s6171 (pattern : Twelve) : d1822 (change pattern 12 6) = d1822 pattern := by
  change (if pattern.j then d1820 (change pattern 12 6) else d1819 (change pattern 12 6)) = d1822 pattern
  rw [s6170, s6167]
  rfl
theorem s6172 (pattern : Twelve) : d1823 (change pattern 12 6) = d1823 pattern := by
  change (if pattern.j then d6 (change pattern 12 6) else d1659 (change pattern 12 6)) = d1823 pattern
  rw [s5921, s6157]
  rfl
theorem s6173 (pattern : Twelve) : d1824 (change pattern 12 6) = d1824 pattern := by
  change (if pattern.d then d1823 (change pattern 12 6) else d1822 (change pattern 12 6)) = d1824 pattern
  rw [s6172, s6171]
  rfl
theorem s6174 (pattern : Twelve) : d1825 (change pattern 12 6) = d1825 pattern := by
  change (if pattern.c then d1824 (change pattern 12 6) else d1821 (change pattern 12 6)) = d1825 pattern
  rw [s6173, s6165]
  rfl
theorem s6175 (pattern : Twelve) : d1826 (change pattern 12 6) = d1825 pattern := by
  change d1825 (change pattern 12 6) = d1825 pattern
  exact s6174 pattern
theorem s6176 (pattern : Twelve) : d1827 (change pattern 12 6) = d3240 pattern := by
  change (if pattern.a then d1826 (change pattern 12 6) else d1664 (change pattern 12 6)) = d3240 pattern
  rw [s6175, s6161]
  rfl
theorem s6177 (pattern : Twelve) : d778 (change pattern 12 12) = d778 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d2 (change pattern 12 12)) = d778 pattern
  rw [s11, s9]
  rfl
theorem s6178 (pattern : Twelve) : d779 (change pattern 12 12) = d779 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d23 (change pattern 12 12)) = d779 pattern
  rw [s11, s29]
  rfl
theorem s6179 (pattern : Twelve) : d782 (change pattern 12 12) = d782 pattern := by
  change (if pattern.h then d779 (change pattern 12 12) else d778 (change pattern 12 12)) = d782 pattern
  rw [s6178, s6177]
  rfl
theorem s6180 (pattern : Twelve) : d788 (change pattern 12 12) = d788 pattern := by
  change (if pattern.f then d782 (change pattern 12 12) else d2 (change pattern 12 12)) = d788 pattern
  rw [s6179, s9]
  rfl
theorem s6181 (pattern : Twelve) : d789 (change pattern 12 12) = d789 pattern := by
  change (if pattern.f then d61 (change pattern 12 12) else d38 (change pattern 12 12)) = d789 pattern
  rw [s368, s44]
  rfl
theorem s6182 (pattern : Twelve) : d794 (change pattern 12 12) = d794 pattern := by
  change (if pattern.e then d789 (change pattern 12 12) else d788 (change pattern 12 12)) = d794 pattern
  rw [s6181, s6180]
  rfl
theorem s6183 (pattern : Twelve) : d783 (change pattern 12 12) = d783 pattern := by
  change (if pattern.h then d44 (change pattern 12 12) else d38 (change pattern 12 12)) = d783 pattern
  rw [s379, s44]
  rfl
theorem s6184 (pattern : Twelve) : d790 (change pattern 12 12) = d790 pattern := by
  change (if pattern.f then d69 (change pattern 12 12) else d783 (change pattern 12 12)) = d790 pattern
  rw [s397, s6183]
  rfl
theorem s6185 (pattern : Twelve) : d795 (change pattern 12 12) = d795 pattern := by
  change (if pattern.e then d90 (change pattern 12 12) else d790 (change pattern 12 12)) = d795 pattern
  rw [s401, s6184]
  rfl
theorem s6186 (pattern : Twelve) : d798 (change pattern 12 12) = d798 pattern := by
  change (if pattern.j then d795 (change pattern 12 12) else d794 (change pattern 12 12)) = d798 pattern
  rw [s6185, s6182]
  rfl
theorem s6187 (pattern : Twelve) : d799 (change pattern 12 12) = d799 pattern := by
  change (if pattern.j then d101 (change pattern 12 12) else d794 (change pattern 12 12)) = d799 pattern
  rw [s402, s6182]
  rfl
theorem s6188 (pattern : Twelve) : d802 (change pattern 12 12) = d802 pattern := by
  change (if pattern.d then d799 (change pattern 12 12) else d798 (change pattern 12 12)) = d802 pattern
  rw [s6187, s6186]
  rfl
theorem s6189 (pattern : Twelve) : d780 (change pattern 12 12) = d780 pattern := by
  change (if pattern.i then d5 (change pattern 12 12) else d3 (change pattern 12 12)) = d780 pattern
  rw [s16, s11]
  rfl
theorem s6190 (pattern : Twelve) : d784 (change pattern 12 12) = d784 pattern := by
  change (if pattern.h then d780 (change pattern 12 12) else d38 (change pattern 12 12)) = d784 pattern
  rw [s6189, s44]
  rfl
theorem s6191 (pattern : Twelve) : d791 (change pattern 12 12) = d791 pattern := by
  change (if pattern.f then d784 (change pattern 12 12) else d38 (change pattern 12 12)) = d791 pattern
  rw [s6190, s44]
  rfl
theorem s6192 (pattern : Twelve) : d796 (change pattern 12 12) = d796 pattern := by
  change (if pattern.e then d90 (change pattern 12 12) else d791 (change pattern 12 12)) = d796 pattern
  rw [s401, s6191]
  rfl
theorem s6193 (pattern : Twelve) : d781 (change pattern 12 12) = d781 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d5 (change pattern 12 12)) = d781 pattern
  rw [s20, s16]
  rfl
theorem s6194 (pattern : Twelve) : d785 (change pattern 12 12) = d785 pattern := by
  change (if pattern.h then d781 (change pattern 12 12) else d48 (change pattern 12 12)) = d785 pattern
  rw [s6193, s87]
  rfl
theorem s6195 (pattern : Twelve) : d792 (change pattern 12 12) = d792 pattern := by
  change (if pattern.f then d785 (change pattern 12 12) else d48 (change pattern 12 12)) = d792 pattern
  rw [s6194, s87]
  rfl
theorem s6196 (pattern : Twelve) : d786 (change pattern 12 12) = d786 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d48 (change pattern 12 12)) = d786 pattern
  rw [s20, s87]
  rfl
theorem s6197 (pattern : Twelve) : d787 (change pattern 12 12) = d787 pattern := by
  change (if pattern.h then d6 (change pattern 12 12) else d49 (change pattern 12 12)) = d787 pattern
  rw [s20, s143]
  rfl
theorem s6198 (pattern : Twelve) : d793 (change pattern 12 12) = d793 pattern := by
  change (if pattern.f then d787 (change pattern 12 12) else d786 (change pattern 12 12)) = d793 pattern
  rw [s6197, s6196]
  rfl
theorem s6199 (pattern : Twelve) : d797 (change pattern 12 12) = d797 pattern := by
  change (if pattern.e then d793 (change pattern 12 12) else d792 (change pattern 12 12)) = d797 pattern
  rw [s6198, s6195]
  rfl
theorem s6200 (pattern : Twelve) : d800 (change pattern 12 12) = d800 pattern := by
  change (if pattern.j then d797 (change pattern 12 12) else d796 (change pattern 12 12)) = d800 pattern
  rw [s6199, s6192]
  rfl
theorem s6201 (pattern : Twelve) : d801 (change pattern 12 12) = d801 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d101 (change pattern 12 12)) = d801 pattern
  rw [s20, s402]
  rfl
theorem s6202 (pattern : Twelve) : d803 (change pattern 12 12) = d803 pattern := by
  change (if pattern.d then d801 (change pattern 12 12) else d800 (change pattern 12 12)) = d803 pattern
  rw [s6201, s6200]
  rfl
theorem s6203 (pattern : Twelve) : d804 (change pattern 12 12) = d804 pattern := by
  change (if pattern.c then d803 (change pattern 12 12) else d802 (change pattern 12 12)) = d804 pattern
  rw [s6202, s6188]
  rfl
theorem s6204 (pattern : Twelve) : d805 (change pattern 12 12) = d805 pattern := by
  change (if pattern.g then d804 (change pattern 12 12) else d155 (change pattern 12 12)) = d805 pattern
  rw [s6203, s4883]
  rfl
theorem s6205 (pattern : Twelve) : d806 (change pattern 12 12) = d806 pattern := by
  change (if pattern.a then d805 (change pattern 12 12) else d116 (change pattern 12 12)) = d806 pattern
  rw [s6204, s407]
  rfl
theorem s6206 (pattern : Twelve) : d1247 (change pattern 12 12) = d1247 pattern := by
  change (if pattern.i then d3 (change pattern 12 12) else d815 (change pattern 12 12)) = d1247 pattern
  rw [s11, s50]
  rfl
theorem s6207 (pattern : Twelve) : d1249 (change pattern 12 12) = d1249 pattern := by
  change (if pattern.h then d1247 (change pattern 12 12) else d779 (change pattern 12 12)) = d1249 pattern
  rw [s6206, s6178]
  rfl
theorem s6208 (pattern : Twelve) : d1253 (change pattern 12 12) = d1253 pattern := by
  change (if pattern.f then d1249 (change pattern 12 12) else d2 (change pattern 12 12)) = d1253 pattern
  rw [s6207, s9]
  rfl
theorem s6209 (pattern : Twelve) : d1248 (change pattern 12 12) = d1248 pattern := by
  change (if pattern.i then d4 (change pattern 12 12) else d23 (change pattern 12 12)) = d1248 pattern
  rw [s14, s29]
  rfl
theorem s6210 (pattern : Twelve) : d1254 (change pattern 12 12) = d1254 pattern := by
  change (if pattern.f then d831 (change pattern 12 12) else d1248 (change pattern 12 12)) = d1254 pattern
  rw [s61, s6209]
  rfl
theorem s6211 (pattern : Twelve) : d1258 (change pattern 12 12) = d1258 pattern := by
  change (if pattern.e then d1254 (change pattern 12 12) else d1253 (change pattern 12 12)) = d1258 pattern
  rw [s6210, s6208]
  rfl
theorem s6212 (pattern : Twelve) : d1261 (change pattern 12 12) = d1261 pattern := by
  change (if pattern.j then d860 (change pattern 12 12) else d1258 (change pattern 12 12)) = d1261 pattern
  rw [s90, s6211]
  rfl
theorem s6213 (pattern : Twelve) : d1250 (change pattern 12 12) = d1250 pattern := by
  change (if pattern.h then d780 (change pattern 12 12) else d41 (change pattern 12 12)) = d1250 pattern
  rw [s6189, s49]
  rfl
theorem s6214 (pattern : Twelve) : d1255 (change pattern 12 12) = d1255 pattern := by
  change (if pattern.f then d1250 (change pattern 12 12) else d38 (change pattern 12 12)) = d1255 pattern
  rw [s6213, s44]
  rfl
theorem s6215 (pattern : Twelve) : d1259 (change pattern 12 12) = d1259 pattern := by
  change (if pattern.e then d852 (change pattern 12 12) else d1255 (change pattern 12 12)) = d1259 pattern
  rw [s89, s6214]
  rfl
theorem s6216 (pattern : Twelve) : d1251 (change pattern 12 12) = d1251 pattern := by
  change (if pattern.h then d781 (change pattern 12 12) else d49 (change pattern 12 12)) = d1251 pattern
  rw [s6193, s143]
  rfl
theorem s6217 (pattern : Twelve) : d1256 (change pattern 12 12) = d1256 pattern := by
  change (if pattern.f then d1251 (change pattern 12 12) else d48 (change pattern 12 12)) = d1256 pattern
  rw [s6216, s87]
  rfl
theorem s6218 (pattern : Twelve) : d1257 (change pattern 12 12) = d1257 pattern := by
  change (if pattern.f then d1252 (change pattern 12 12) else d787 (change pattern 12 12)) = d1257 pattern
  rw [s254, s6197]
  rfl
theorem s6219 (pattern : Twelve) : d1260 (change pattern 12 12) = d1260 pattern := by
  change (if pattern.e then d1257 (change pattern 12 12) else d1256 (change pattern 12 12)) = d1260 pattern
  rw [s6218, s6217]
  rfl
theorem s6220 (pattern : Twelve) : d1262 (change pattern 12 12) = d1262 pattern := by
  change (if pattern.j then d1260 (change pattern 12 12) else d1259 (change pattern 12 12)) = d1262 pattern
  rw [s6219, s6215]
  rfl
theorem s6221 (pattern : Twelve) : d1263 (change pattern 12 12) = d1263 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d860 (change pattern 12 12)) = d1263 pattern
  rw [s20, s90]
  rfl
theorem s6222 (pattern : Twelve) : d1264 (change pattern 12 12) = d1264 pattern := by
  change (if pattern.d then d1263 (change pattern 12 12) else d1262 (change pattern 12 12)) = d1264 pattern
  rw [s6221, s6220]
  rfl
theorem s6223 (pattern : Twelve) : d1265 (change pattern 12 12) = d1265 pattern := by
  change (if pattern.c then d1264 (change pattern 12 12) else d1261 (change pattern 12 12)) = d1265 pattern
  rw [s6222, s6212]
  rfl
theorem s6224 (pattern : Twelve) : d1266 (change pattern 12 12) = d1266 pattern := by
  change (if pattern.g then d1265 (change pattern 12 12) else d906 (change pattern 12 12)) = d1266 pattern
  rw [s6223, s212]
  rfl
theorem s6225 (pattern : Twelve) : d1267 (change pattern 12 12) = d1267 pattern := by
  change (if pattern.a then d1266 (change pattern 12 12) else d871 (change pattern 12 12)) = d1267 pattern
  rw [s6224, s95]
  rfl
theorem s6226 (pattern : Twelve) : d1616 (change pattern 12 12) = d1616 pattern := by
  change (if pattern.i then d119 (change pattern 12 12) else d1276 (change pattern 12 12)) = d1616 pattern
  rw [s115, s105]
  rfl
theorem s6227 (pattern : Twelve) : d1619 (change pattern 12 12) = d1619 pattern := by
  change (if pattern.h then d119 (change pattern 12 12) else d1616 (change pattern 12 12)) = d1619 pattern
  rw [s115, s6226]
  rfl
theorem s6228 (pattern : Twelve) : d1622 (change pattern 12 12) = d1622 pattern := by
  change (if pattern.f then d1619 (change pattern 12 12) else d23 (change pattern 12 12)) = d1622 pattern
  rw [s6227, s29]
  rfl
theorem s6229 (pattern : Twelve) : d1617 (change pattern 12 12) = d1617 pattern := by
  change (if pattern.i then d24 (change pattern 12 12) else d25 (change pattern 12 12)) = d1617 pattern
  rw [s48, s18]
  rfl
theorem s6230 (pattern : Twelve) : d1623 (change pattern 12 12) = d1623 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d1617 (change pattern 12 12)) = d1623 pattern
  rw [s20, s6229]
  rfl
theorem s6231 (pattern : Twelve) : d1627 (change pattern 12 12) = d1627 pattern := by
  change (if pattern.e then d1623 (change pattern 12 12) else d1622 (change pattern 12 12)) = d1627 pattern
  rw [s6230, s6228]
  rfl
theorem s6232 (pattern : Twelve) : d1630 (change pattern 12 12) = d1630 pattern := by
  change (if pattern.j then d1312 (change pattern 12 12) else d1627 (change pattern 12 12)) = d1630 pattern
  rw [s146, s6231]
  rfl
theorem s6233 (pattern : Twelve) : d1618 (change pattern 12 12) = d1618 pattern := by
  change (if pattern.i then d118 (change pattern 12 12) else d119 (change pattern 12 12)) = d1618 pattern
  rw [s203, s115]
  rfl
theorem s6234 (pattern : Twelve) : d1620 (change pattern 12 12) = d1620 pattern := by
  change (if pattern.h then d1618 (change pattern 12 12) else d1282 (change pattern 12 12)) = d1620 pattern
  rw [s6233, s122]
  rfl
theorem s6235 (pattern : Twelve) : d1624 (change pattern 12 12) = d1624 pattern := by
  change (if pattern.f then d1620 (change pattern 12 12) else d41 (change pattern 12 12)) = d1624 pattern
  rw [s6234, s49]
  rfl
theorem s6236 (pattern : Twelve) : d1628 (change pattern 12 12) = d1628 pattern := by
  change (if pattern.e then d1304 (change pattern 12 12) else d1624 (change pattern 12 12)) = d1628 pattern
  rw [s145, s6235]
  rfl
theorem s6237 (pattern : Twelve) : d182 (change pattern 12 12) = d182 pattern := by
  change (if pattern.i then d6 (change pattern 12 12) else d118 (change pattern 12 12)) = d182 pattern
  rw [s20, s203]
  rfl
theorem s6238 (pattern : Twelve) : d1621 (change pattern 12 12) = d1621 pattern := by
  change (if pattern.h then d182 (change pattern 12 12) else d1331 (change pattern 12 12)) = d1621 pattern
  rw [s6237, s232]
  rfl
theorem s6239 (pattern : Twelve) : d1625 (change pattern 12 12) = d1625 pattern := by
  change (if pattern.f then d1621 (change pattern 12 12) else d49 (change pattern 12 12)) = d1625 pattern
  rw [s6238, s143]
  rfl
theorem s6240 (pattern : Twelve) : d1629 (change pattern 12 12) = d1629 pattern := by
  change (if pattern.e then d1626 (change pattern 12 12) else d1625 (change pattern 12 12)) = d1629 pattern
  rw [s255, s6239]
  rfl
theorem s6241 (pattern : Twelve) : d1631 (change pattern 12 12) = d1631 pattern := by
  change (if pattern.j then d1629 (change pattern 12 12) else d1628 (change pattern 12 12)) = d1631 pattern
  rw [s6240, s6236]
  rfl
theorem s6242 (pattern : Twelve) : d1632 (change pattern 12 12) = d1632 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1312 (change pattern 12 12)) = d1632 pattern
  rw [s20, s146]
  rfl
theorem s6243 (pattern : Twelve) : d1633 (change pattern 12 12) = d1633 pattern := by
  change (if pattern.d then d1632 (change pattern 12 12) else d1631 (change pattern 12 12)) = d1633 pattern
  rw [s6242, s6241]
  rfl
theorem s6244 (pattern : Twelve) : d1634 (change pattern 12 12) = d1634 pattern := by
  change (if pattern.c then d1633 (change pattern 12 12) else d1630 (change pattern 12 12)) = d1634 pattern
  rw [s6243, s6232]
  rfl
theorem s6245 (pattern : Twelve) : d1635 (change pattern 12 12) = d1635 pattern := by
  change (if pattern.g then d1634 (change pattern 12 12) else d1353 (change pattern 12 12)) = d1635 pattern
  rw [s6244, s242]
  rfl
theorem s6246 (pattern : Twelve) : d1636 (change pattern 12 12) = d1636 pattern := by
  change (if pattern.a then d1635 (change pattern 12 12) else d1323 (change pattern 12 12)) = d1636 pattern
  rw [s6245, s151]
  rfl
theorem s6247 (pattern : Twelve) : d1814 (change pattern 12 12) = d1814 pattern := by
  change (if pattern.f then d20 (change pattern 12 12) else d25 (change pattern 12 12)) = d1814 pattern
  rw [s156, s18]
  rfl
theorem s6248 (pattern : Twelve) : d1815 (change pattern 12 12) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 12 12) else d21 (change pattern 12 12)) = d1815 pattern
  rw [s20, s58]
  rfl
theorem s6249 (pattern : Twelve) : d1818 (change pattern 12 12) = d1818 pattern := by
  change (if pattern.e then d1815 (change pattern 12 12) else d1814 (change pattern 12 12)) = d1818 pattern
  rw [s6248, s6247]
  rfl
theorem s6250 (pattern : Twelve) : d1821 (change pattern 12 12) = d1821 pattern := by
  change (if pattern.j then d1659 (change pattern 12 12) else d1818 (change pattern 12 12)) = d1821 pattern
  rw [s172, s6249]
  rfl
theorem s6251 (pattern : Twelve) : d1816 (change pattern 12 12) = d1816 pattern := by
  change (if pattern.f then d1646 (change pattern 12 12) else d821 (change pattern 12 12)) = d1816 pattern
  rw [s167, s59]
  rfl
theorem s6252 (pattern : Twelve) : d1819 (change pattern 12 12) = d1819 pattern := by
  change (if pattern.e then d1655 (change pattern 12 12) else d1816 (change pattern 12 12)) = d1819 pattern
  rw [s171, s6251]
  rfl
theorem s6253 (pattern : Twelve) : d1817 (change pattern 12 12) = d1817 pattern := by
  change (if pattern.f then d183 (change pattern 12 12) else d822 (change pattern 12 12)) = d1817 pattern
  rw [s251, s60]
  rfl
theorem s6254 (pattern : Twelve) : d1820 (change pattern 12 12) = d1820 pattern := by
  change (if pattern.e then d6 (change pattern 12 12) else d1817 (change pattern 12 12)) = d1820 pattern
  rw [s20, s6253]
  rfl
theorem s6255 (pattern : Twelve) : d1822 (change pattern 12 12) = d1822 pattern := by
  change (if pattern.j then d1820 (change pattern 12 12) else d1819 (change pattern 12 12)) = d1822 pattern
  rw [s6254, s6252]
  rfl
theorem s6256 (pattern : Twelve) : d1823 (change pattern 12 12) = d1823 pattern := by
  change (if pattern.j then d6 (change pattern 12 12) else d1659 (change pattern 12 12)) = d1823 pattern
  rw [s20, s172]
  rfl
theorem s6257 (pattern : Twelve) : d1824 (change pattern 12 12) = d1824 pattern := by
  change (if pattern.d then d1823 (change pattern 12 12) else d1822 (change pattern 12 12)) = d1824 pattern
  rw [s6256, s6255]
  rfl
theorem s6258 (pattern : Twelve) : d1825 (change pattern 12 12) = d1825 pattern := by
  change (if pattern.c then d1824 (change pattern 12 12) else d1821 (change pattern 12 12)) = d1825 pattern
  rw [s6257, s6250]
  rfl
theorem s6259 (pattern : Twelve) : d1826 (change pattern 12 12) = d1826 pattern := by
  change (if pattern.g then d1825 (change pattern 12 12) else d1677 (change pattern 12 12)) = d1826 pattern
  rw [s6258, s259]
  rfl
theorem s6260 (pattern : Twelve) : d1827 (change pattern 12 12) = d1827 pattern := by
  change (if pattern.a then d1826 (change pattern 12 12) else d1664 (change pattern 12 12)) = d1827 pattern
  rw [s6259, s176]
  rfl
theorem s6261 (pattern : Twelve) : d0 (change pattern 12 0) = d0 pattern := by
  rfl
theorem s6262 (pattern : Twelve) : d1 (change pattern 12 0) = d1 pattern := by
  rfl
theorem s6263 (pattern : Twelve) : d26 (change pattern 12 0) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 12 0) else d0 (change pattern 12 0)) = d26 pattern
  rw [s6262, s6261]
  rfl
theorem s6264 (pattern : Twelve) : d7 (change pattern 12 0) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 12 0) else d0 (change pattern 12 0)) = d7 pattern
  rw [s6262, s6261]
  rfl
theorem s6265 (pattern : Twelve) : d17 (change pattern 12 0) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 12 0) else d0 (change pattern 12 0)) = d17 pattern
  rw [s6264, s6261]
  rfl
theorem s6266 (pattern : Twelve) : d27 (change pattern 12 0) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 12 0) else d17 (change pattern 12 0)) = d27 pattern
  rw [s6262, s6265]
  rfl
theorem s6267 (pattern : Twelve) : d50 (change pattern 12 0) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 12 0) else d26 (change pattern 12 0)) = d50 pattern
  rw [s6266, s6263]
  rfl
theorem s6268 (pattern : Twelve) : d72 (change pattern 12 0) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 12 0) else d0 (change pattern 12 0)) = d72 pattern
  rw [s6267, s6261]
  rfl
theorem s6269 (pattern : Twelve) : d2 (change pattern 12 0) = d2 pattern := by
  rfl
theorem s6270 (pattern : Twelve) : d8 (change pattern 12 0) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 12 0) else d1 (change pattern 12 0)) = d8 pattern
  rw [s6269, s6262]
  rfl
theorem s6271 (pattern : Twelve) : d3 (change pattern 12 0) = d3 pattern := by
  rfl
theorem s6272 (pattern : Twelve) : d9 (change pattern 12 0) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 12 0) else d2 (change pattern 12 0)) = d9 pattern
  rw [s6271, s6269]
  rfl
theorem s6273 (pattern : Twelve) : d18 (change pattern 12 0) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 12 0) else d8 (change pattern 12 0)) = d18 pattern
  rw [s6272, s6270]
  rfl
theorem s6274 (pattern : Twelve) : d28 (change pattern 12 0) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 12 0) else d17 (change pattern 12 0)) = d28 pattern
  rw [s6273, s6265]
  rfl
theorem s6275 (pattern : Twelve) : d10 (change pattern 12 0) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 12 0) else d0 (change pattern 12 0)) = d10 pattern
  rw [s6269, s6261]
  rfl
theorem s6276 (pattern : Twelve) : d11 (change pattern 12 0) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 12 0) else d1 (change pattern 12 0)) = d11 pattern
  rw [s6271, s6262]
  rfl
theorem s6277 (pattern : Twelve) : d19 (change pattern 12 0) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 12 0) else d10 (change pattern 12 0)) = d19 pattern
  rw [s6276, s6275]
  rfl
theorem s6278 (pattern : Twelve) : d6 (change pattern 12 0) = d6 pattern := by
  rfl
theorem s6279 (pattern : Twelve) : d29 (change pattern 12 0) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 12 0) else d19 (change pattern 12 0)) = d29 pattern
  rw [s6278, s6277]
  rfl
theorem s6280 (pattern : Twelve) : d51 (change pattern 12 0) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 12 0) else d28 (change pattern 12 0)) = d51 pattern
  rw [s6279, s6274]
  rfl
theorem s6281 (pattern : Twelve) : d73 (change pattern 12 0) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 12 0) else d0 (change pattern 12 0)) = d73 pattern
  rw [s6280, s6261]
  rfl
theorem s6282 (pattern : Twelve) : d91 (change pattern 12 0) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 12 0) else d72 (change pattern 12 0)) = d91 pattern
  rw [s6281, s6268]
  rfl
theorem s6283 (pattern : Twelve) : d30 (change pattern 12 0) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 12 0) else d0 (change pattern 12 0)) = d30 pattern
  rw [s6269, s6261]
  rfl
theorem s6284 (pattern : Twelve) : d5 (change pattern 12 0) = d5 pattern := by
  rfl
theorem s6285 (pattern : Twelve) : d12 (change pattern 12 0) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 12 0) else d3 (change pattern 12 0)) = d12 pattern
  rw [s6284, s6271]
  rfl
theorem s6286 (pattern : Twelve) : d4 (change pattern 12 0) = d4 pattern := by
  rfl
theorem s6287 (pattern : Twelve) : d13 (change pattern 12 0) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 12 0) else d4 (change pattern 12 0)) = d13 pattern
  rw [s6278, s6286]
  rfl
theorem s6288 (pattern : Twelve) : d20 (change pattern 12 0) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 12 0) else d12 (change pattern 12 0)) = d20 pattern
  rw [s6287, s6285]
  rfl
theorem s6289 (pattern : Twelve) : d31 (change pattern 12 0) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 12 0) else d0 (change pattern 12 0)) = d31 pattern
  rw [s6288, s6261]
  rfl
theorem s6290 (pattern : Twelve) : d52 (change pattern 12 0) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 12 0) else d30 (change pattern 12 0)) = d52 pattern
  rw [s6289, s6283]
  rfl
theorem s6291 (pattern : Twelve) : d14 (change pattern 12 0) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 12 0) else d5 (change pattern 12 0)) = d14 pattern
  rw [s6278, s6284]
  rfl
theorem s6292 (pattern : Twelve) : d21 (change pattern 12 0) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 12 0) else d13 (change pattern 12 0)) = d21 pattern
  rw [s6291, s6287]
  rfl
theorem s6293 (pattern : Twelve) : d32 (change pattern 12 0) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 12 0) else d17 (change pattern 12 0)) = d32 pattern
  rw [s6292, s6265]
  rfl
theorem s6294 (pattern : Twelve) : d53 (change pattern 12 0) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 12 0) else d30 (change pattern 12 0)) = d53 pattern
  rw [s6293, s6283]
  rfl
theorem s6295 (pattern : Twelve) : d74 (change pattern 12 0) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 12 0) else d52 (change pattern 12 0)) = d74 pattern
  rw [s6294, s6290]
  rfl
theorem s6296 (pattern : Twelve) : d22 (change pattern 12 0) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 12 0) else d14 (change pattern 12 0)) = d22 pattern
  rw [s6278, s6291]
  rfl
theorem s6297 (pattern : Twelve) : d33 (change pattern 12 0) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 12 0) else d0 (change pattern 12 0)) = d33 pattern
  rw [s6296, s6261]
  rfl
theorem s6298 (pattern : Twelve) : d54 (change pattern 12 0) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 12 0) else d30 (change pattern 12 0)) = d54 pattern
  rw [s6297, s6283]
  rfl
theorem s6299 (pattern : Twelve) : d23 (change pattern 12 0) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 12 0) else d2 (change pattern 12 0)) = d23 pattern
  rw [s6272, s6269]
  rfl
end NetHack.Sokoban21.Diagram
