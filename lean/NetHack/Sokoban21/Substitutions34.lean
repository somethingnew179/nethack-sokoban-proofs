/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions33
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s5100 (pattern : Twelve) : d1347 (change pattern 12 5) = d3215 pattern := by
  change (if pattern.e then d1342 (change pattern 12 5) else d1341 (change pattern 12 5)) = d3215 pattern
  rw [s5099, s5098]
  rfl
theorem s5101 (pattern : Twelve) : d1330 (change pattern 12 5) = d1330 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d1276 (change pattern 12 5)) = d1330 pattern
  rw [s4902, s5062]
  rfl
theorem s5102 (pattern : Twelve) : d1331 (change pattern 12 5) = d1331 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d1277 (change pattern 12 5)) = d1331 pattern
  rw [s4902, s5075]
  rfl
theorem s5103 (pattern : Twelve) : d1337 (change pattern 12 5) = d1337 pattern := by
  change (if pattern.h then d1331 (change pattern 12 5) else d1330 (change pattern 12 5)) = d1337 pattern
  rw [s5102, s5101]
  rfl
theorem s5104 (pattern : Twelve) : d1343 (change pattern 12 5) = d1337 pattern := by
  change d1337 (change pattern 12 5) = d1337 pattern
  exact s5103 pattern
theorem s5105 (pattern : Twelve) : d1344 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5106 (pattern : Twelve) : d1348 (change pattern 12 5) = d3216 pattern := by
  change (if pattern.e then d1344 (change pattern 12 5) else d1343 (change pattern 12 5)) = d3216 pattern
  rw [s5105, s5104]
  rfl
theorem s5107 (pattern : Twelve) : d1350 (change pattern 12 5) = d3217 pattern := by
  change (if pattern.j then d1348 (change pattern 12 5) else d1347 (change pattern 12 5)) = d3217 pattern
  rw [s5106, s5100]
  rfl
theorem s5108 (pattern : Twelve) : d1351 (change pattern 12 5) = d3218 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d1346 (change pattern 12 5)) = d3218 pattern
  rw [s4902, s5094]
  rfl
theorem s5109 (pattern : Twelve) : d1352 (change pattern 12 5) = d3219 pattern := by
  change (if pattern.d then d1351 (change pattern 12 5) else d1350 (change pattern 12 5)) = d3219 pattern
  rw [s5108, s5107]
  rfl
theorem s5110 (pattern : Twelve) : d1353 (change pattern 12 5) = d3220 pattern := by
  change (if pattern.c then d1352 (change pattern 12 5) else d1349 (change pattern 12 5)) = d3220 pattern
  rw [s5109, s5095]
  rfl
theorem s5111 (pattern : Twelve) : d1354 (change pattern 12 5) = d3221 pattern := by
  change (if pattern.a then d1353 (change pattern 12 5) else d1321 (change pattern 12 5)) = d3221 pattern
  rw [s5110, s5084]
  rfl
theorem s5112 (pattern : Twelve) : d1649 (change pattern 12 5) = d1324 pattern := by
  change d1324 (change pattern 12 5) = d1324 pattern
  exact s5085 pattern
theorem s5113 (pattern : Twelve) : d1650 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5114 (pattern : Twelve) : d1656 (change pattern 12 5) = d2404 pattern := by
  change (if pattern.e then d1650 (change pattern 12 5) else d1649 (change pattern 12 5)) = d2404 pattern
  rw [s5113, s5112]
  rfl
theorem s5115 (pattern : Twelve) : d1644 (change pattern 12 5) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 12 5) else d1324 (change pattern 12 5)) = d1644 pattern
  rw [s4982, s5085]
  rfl
theorem s5116 (pattern : Twelve) : d1645 (change pattern 12 5) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d1324 (change pattern 12 5)) = d1645 pattern
  rw [s4902, s5085]
  rfl
theorem s5117 (pattern : Twelve) : d1647 (change pattern 12 5) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 12 5) else d1644 (change pattern 12 5)) = d1647 pattern
  rw [s5116, s5115]
  rfl
theorem s5118 (pattern : Twelve) : d1651 (change pattern 12 5) = d1647 pattern := by
  change d1647 (change pattern 12 5) = d1647 pattern
  exact s5117 pattern
theorem s5119 (pattern : Twelve) : d1657 (change pattern 12 5) = d3222 pattern := by
  change (if pattern.e then d1300 (change pattern 12 5) else d1651 (change pattern 12 5)) = d3222 pattern
  rw [s5079, s5118]
  rfl
theorem s5120 (pattern : Twelve) : d1660 (change pattern 12 5) = d3223 pattern := by
  change (if pattern.j then d1657 (change pattern 12 5) else d1656 (change pattern 12 5)) = d3223 pattern
  rw [s5119, s5114]
  rfl
theorem s5121 (pattern : Twelve) : d1652 (change pattern 12 5) = d1644 pattern := by
  change d1644 (change pattern 12 5) = d1644 pattern
  exact s5115 pattern
theorem s5122 (pattern : Twelve) : d1653 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5123 (pattern : Twelve) : d1658 (change pattern 12 5) = d3224 pattern := by
  change (if pattern.e then d1653 (change pattern 12 5) else d1652 (change pattern 12 5)) = d3224 pattern
  rw [s5122, s5121]
  rfl
theorem s5124 (pattern : Twelve) : d1646 (change pattern 12 5) = d1646 pattern := by
  change (if pattern.i then d22 (change pattern 12 5) else d20 (change pattern 12 5)) = d1646 pattern
  rw [s4980, s4982]
  rfl
theorem s5125 (pattern : Twelve) : d1648 (change pattern 12 5) = d1648 pattern := by
  change (if pattern.h then d128 (change pattern 12 5) else d1646 (change pattern 12 5)) = d1648 pattern
  rw [s4983, s5124]
  rfl
theorem s5126 (pattern : Twelve) : d1654 (change pattern 12 5) = d1648 pattern := by
  change d1648 (change pattern 12 5) = d1648 pattern
  exact s5125 pattern
theorem s5127 (pattern : Twelve) : d1655 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5128 (pattern : Twelve) : d1659 (change pattern 12 5) = d3225 pattern := by
  change (if pattern.e then d1655 (change pattern 12 5) else d1654 (change pattern 12 5)) = d3225 pattern
  rw [s5127, s5126]
  rfl
theorem s5129 (pattern : Twelve) : d1661 (change pattern 12 5) = d3226 pattern := by
  change (if pattern.j then d1659 (change pattern 12 5) else d1658 (change pattern 12 5)) = d3226 pattern
  rw [s5128, s5123]
  rfl
theorem s5130 (pattern : Twelve) : d1662 (change pattern 12 5) = d3227 pattern := by
  change (if pattern.j then d6 (change pattern 12 5) else d1657 (change pattern 12 5)) = d3227 pattern
  rw [s4902, s5119]
  rfl
theorem s5131 (pattern : Twelve) : d1663 (change pattern 12 5) = d3228 pattern := by
  change (if pattern.d then d1662 (change pattern 12 5) else d1661 (change pattern 12 5)) = d3228 pattern
  rw [s5130, s5129]
  rfl
theorem s5132 (pattern : Twelve) : d1664 (change pattern 12 5) = d3229 pattern := by
  change (if pattern.c then d1663 (change pattern 12 5) else d1660 (change pattern 12 5)) = d3229 pattern
  rw [s5131, s5120]
  rfl
theorem s5133 (pattern : Twelve) : d1668 (change pattern 12 5) = d1644 pattern := by
  change d1644 (change pattern 12 5) = d1644 pattern
  exact s5115 pattern
theorem s5134 (pattern : Twelve) : d1671 (change pattern 12 5) = d3224 pattern := by
  change (if pattern.e then d1650 (change pattern 12 5) else d1668 (change pattern 12 5)) = d3224 pattern
  rw [s5113, s5133]
  rfl
theorem s5135 (pattern : Twelve) : d1674 (change pattern 12 5) = d3230 pattern := by
  change (if pattern.j then d1657 (change pattern 12 5) else d1671 (change pattern 12 5)) = d3230 pattern
  rw [s5119, s5134]
  rfl
theorem s5136 (pattern : Twelve) : d1665 (change pattern 12 5) = d1665 pattern := by
  change (if pattern.i then d22 (change pattern 12 5) else d1324 (change pattern 12 5)) = d1665 pattern
  rw [s4980, s5085]
  rfl
theorem s5137 (pattern : Twelve) : d1666 (change pattern 12 5) = d1666 pattern := by
  change (if pattern.h then d1665 (change pattern 12 5) else d1644 (change pattern 12 5)) = d1666 pattern
  rw [s5136, s5115]
  rfl
theorem s5138 (pattern : Twelve) : d1669 (change pattern 12 5) = d1666 pattern := by
  change d1666 (change pattern 12 5) = d1666 pattern
  exact s5137 pattern
theorem s5139 (pattern : Twelve) : d1672 (change pattern 12 5) = d3231 pattern := by
  change (if pattern.e then d1300 (change pattern 12 5) else d1669 (change pattern 12 5)) = d3231 pattern
  rw [s5079, s5138]
  rfl
theorem s5140 (pattern : Twelve) : d183 (change pattern 12 5) = d183 pattern := by
  change (if pattern.i then d6 (change pattern 12 5) else d22 (change pattern 12 5)) = d183 pattern
  rw [s4902, s4980]
  rfl
theorem s5141 (pattern : Twelve) : d1667 (change pattern 12 5) = d1667 pattern := by
  change (if pattern.h then d183 (change pattern 12 5) else d128 (change pattern 12 5)) = d1667 pattern
  rw [s5140, s4983]
  rfl
theorem s5142 (pattern : Twelve) : d1670 (change pattern 12 5) = d1667 pattern := by
  change d1667 (change pattern 12 5) = d1667 pattern
  exact s5141 pattern
theorem s5143 (pattern : Twelve) : d1626 (change pattern 12 5) = d6 pattern := by
  change d6 (change pattern 12 5) = d6 pattern
  exact s4902 pattern
theorem s5144 (pattern : Twelve) : d1673 (change pattern 12 5) = d3232 pattern := by
  change (if pattern.e then d1626 (change pattern 12 5) else d1670 (change pattern 12 5)) = d3232 pattern
  rw [s5143, s5142]
  rfl
theorem s5145 (pattern : Twelve) : d1675 (change pattern 12 5) = d3233 pattern := by
  change (if pattern.j then d1673 (change pattern 12 5) else d1672 (change pattern 12 5)) = d3233 pattern
  rw [s5144, s5139]
  rfl
theorem s5146 (pattern : Twelve) : d1676 (change pattern 12 5) = d3234 pattern := by
  change (if pattern.d then d1662 (change pattern 12 5) else d1675 (change pattern 12 5)) = d3234 pattern
  rw [s5130, s5145]
  rfl
theorem s5147 (pattern : Twelve) : d1677 (change pattern 12 5) = d3235 pattern := by
  change (if pattern.c then d1676 (change pattern 12 5) else d1674 (change pattern 12 5)) = d3235 pattern
  rw [s5146, s5135]
  rfl
theorem s5148 (pattern : Twelve) : d1678 (change pattern 12 5) = d3236 pattern := by
  change (if pattern.a then d1677 (change pattern 12 5) else d1664 (change pattern 12 5)) = d3236 pattern
  rw [s5147, s5132]
  rfl
theorem s5149 (pattern : Twelve) : d0 (change pattern 6 12) = d0 pattern := by
  rfl
theorem s5150 (pattern : Twelve) : d1 (change pattern 6 12) = d1 pattern := by
  rfl
theorem s5151 (pattern : Twelve) : d7 (change pattern 6 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 6 12) else d0 (change pattern 6 12)) = d7 pattern
  rw [s5150, s5149]
  rfl
theorem s5152 (pattern : Twelve) : d17 (change pattern 6 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 6 12) else d0 (change pattern 6 12)) = d17 pattern
  rw [s5151, s5149]
  rfl
theorem s5153 (pattern : Twelve) : d27 (change pattern 6 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 6 12) else d17 (change pattern 6 12)) = d27 pattern
  rw [s5150, s5152]
  rfl
theorem s5154 (pattern : Twelve) : d814 (change pattern 6 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 6 12) else d7 (change pattern 6 12)) = d814 pattern
  rw [s5150, s5151]
  rfl
theorem s5155 (pattern : Twelve) : d816 (change pattern 6 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 6 12) else d814 (change pattern 6 12)) = d816 pattern
  rw [s5150, s5154]
  rfl
theorem s5156 (pattern : Twelve) : d824 (change pattern 6 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 6 12) else d27 (change pattern 6 12)) = d824 pattern
  rw [s5155, s5153]
  rfl
theorem s5157 (pattern : Twelve) : d838 (change pattern 6 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 6 12) else d0 (change pattern 6 12)) = d838 pattern
  rw [s5156, s5149]
  rfl
theorem s5158 (pattern : Twelve) : d2 (change pattern 6 12) = d2 pattern := by
  rfl
theorem s5159 (pattern : Twelve) : d10 (change pattern 6 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 6 12) else d0 (change pattern 6 12)) = d10 pattern
  rw [s5158, s5149]
  rfl
theorem s5160 (pattern : Twelve) : d3 (change pattern 6 12) = d3 pattern := by
  rfl
theorem s5161 (pattern : Twelve) : d11 (change pattern 6 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 6 12) else d1 (change pattern 6 12)) = d11 pattern
  rw [s5160, s5150]
  rfl
theorem s5162 (pattern : Twelve) : d19 (change pattern 6 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 6 12) else d10 (change pattern 6 12)) = d19 pattern
  rw [s5161, s5159]
  rfl
theorem s5163 (pattern : Twelve) : d4 (change pattern 6 12) = d4 pattern := by
  rfl
theorem s5164 (pattern : Twelve) : d16 (change pattern 6 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 6 12) else d2 (change pattern 6 12)) = d16 pattern
  rw [s5163, s5158]
  rfl
theorem s5165 (pattern : Twelve) : d5 (change pattern 6 12) = d5 pattern := by
  rfl
theorem s5166 (pattern : Twelve) : d12 (change pattern 6 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 6 12) else d3 (change pattern 6 12)) = d12 pattern
  rw [s5165, s5160]
  rfl
theorem s5167 (pattern : Twelve) : d25 (change pattern 6 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 6 12) else d16 (change pattern 6 12)) = d25 pattern
  rw [s5166, s5164]
  rfl
theorem s5168 (pattern : Twelve) : d817 (change pattern 6 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 6 12) else d19 (change pattern 6 12)) = d817 pattern
  rw [s5167, s5162]
  rfl
theorem s5169 (pattern : Twelve) : d6 (change pattern 6 12) = d6 pattern := by
  rfl
theorem s5170 (pattern : Twelve) : d42 (change pattern 6 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d25 (change pattern 6 12)) = d42 pattern
  rw [s5169, s5167]
  rfl
theorem s5171 (pattern : Twelve) : d825 (change pattern 6 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 6 12) else d817 (change pattern 6 12)) = d825 pattern
  rw [s5170, s5168]
  rfl
theorem s5172 (pattern : Twelve) : d839 (change pattern 6 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 6 12) else d17 (change pattern 6 12)) = d839 pattern
  rw [s5171, s5152]
  rfl
theorem s5173 (pattern : Twelve) : d853 (change pattern 6 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 6 12) else d838 (change pattern 6 12)) = d853 pattern
  rw [s5172, s5157]
  rfl
theorem s5174 (pattern : Twelve) : d30 (change pattern 6 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 6 12) else d0 (change pattern 6 12)) = d30 pattern
  rw [s5158, s5149]
  rfl
theorem s5175 (pattern : Twelve) : d35 (change pattern 6 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d0 (change pattern 6 12)) = d35 pattern
  rw [s5169, s5149]
  rfl
theorem s5176 (pattern : Twelve) : d56 (change pattern 6 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 6 12) else d30 (change pattern 6 12)) = d56 pattern
  rw [s5175, s5174]
  rfl
theorem s5177 (pattern : Twelve) : d9 (change pattern 6 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 6 12) else d2 (change pattern 6 12)) = d9 pattern
  rw [s5160, s5158]
  rfl
theorem s5178 (pattern : Twelve) : d23 (change pattern 6 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 6 12) else d2 (change pattern 6 12)) = d23 pattern
  rw [s5177, s5158]
  rfl
theorem s5179 (pattern : Twelve) : d34 (change pattern 6 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 6 12) else d17 (change pattern 6 12)) = d34 pattern
  rw [s5178, s5152]
  rfl
theorem s5180 (pattern : Twelve) : d818 (change pattern 6 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d814 (change pattern 6 12)) = d818 pattern
  rw [s5169, s5154]
  rfl
theorem s5181 (pattern : Twelve) : d826 (change pattern 6 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 6 12) else d34 (change pattern 6 12)) = d826 pattern
  rw [s5180, s5179]
  rfl
theorem s5182 (pattern : Twelve) : d840 (change pattern 6 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 6 12) else d56 (change pattern 6 12)) = d840 pattern
  rw [s5181, s5176]
  rfl
theorem s5183 (pattern : Twelve) : d36 (change pattern 6 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d17 (change pattern 6 12)) = d36 pattern
  rw [s5169, s5152]
  rfl
theorem s5184 (pattern : Twelve) : d827 (change pattern 6 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 6 12) else d34 (change pattern 6 12)) = d827 pattern
  rw [s5183, s5179]
  rfl
theorem s5185 (pattern : Twelve) : d841 (change pattern 6 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 6 12) else d827 (change pattern 6 12)) = d841 pattern
  rw [s5171, s5184]
  rfl
theorem s5186 (pattern : Twelve) : d854 (change pattern 6 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 6 12) else d840 (change pattern 6 12)) = d854 pattern
  rw [s5185, s5182]
  rfl
theorem s5187 (pattern : Twelve) : d861 (change pattern 6 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 6 12) else d853 (change pattern 6 12)) = d861 pattern
  rw [s5186, s5173]
  rfl
theorem s5188 (pattern : Twelve) : d819 (change pattern 6 12) = d819 pattern := by
  change (if pattern.i then d3 (change pattern 6 12) else d814 (change pattern 6 12)) = d819 pattern
  rw [s5160, s5154]
  rfl
theorem s5189 (pattern : Twelve) : d828 (change pattern 6 12) = d828 pattern := by
  change (if pattern.h then d819 (change pattern 6 12) else d34 (change pattern 6 12)) = d828 pattern
  rw [s5188, s5179]
  rfl
theorem s5190 (pattern : Twelve) : d842 (change pattern 6 12) = d842 pattern := by
  change (if pattern.f then d828 (change pattern 6 12) else d30 (change pattern 6 12)) = d842 pattern
  rw [s5189, s5174]
  rfl
theorem s5191 (pattern : Twelve) : d843 (change pattern 6 12) = d843 pattern := by
  change (if pattern.f then d825 (change pattern 6 12) else d34 (change pattern 6 12)) = d843 pattern
  rw [s5171, s5179]
  rfl
theorem s5192 (pattern : Twelve) : d855 (change pattern 6 12) = d855 pattern := by
  change (if pattern.e then d843 (change pattern 6 12) else d842 (change pattern 6 12)) = d855 pattern
  rw [s5191, s5190]
  rfl
theorem s5193 (pattern : Twelve) : d38 (change pattern 6 12) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 6 12) else d2 (change pattern 6 12)) = d38 pattern
  rw [s5163, s5158]
  rfl
theorem s5194 (pattern : Twelve) : d39 (change pattern 6 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d2 (change pattern 6 12)) = d39 pattern
  rw [s5169, s5158]
  rfl
theorem s5195 (pattern : Twelve) : d59 (change pattern 6 12) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 6 12) else d38 (change pattern 6 12)) = d59 pattern
  rw [s5194, s5193]
  rfl
theorem s5196 (pattern : Twelve) : d15 (change pattern 6 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 6 12) else d4 (change pattern 6 12)) = d15 pattern
  rw [s5165, s5163]
  rfl
theorem s5197 (pattern : Twelve) : d24 (change pattern 6 12) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 6 12) else d4 (change pattern 6 12)) = d24 pattern
  rw [s5196, s5163]
  rfl
theorem s5198 (pattern : Twelve) : d41 (change pattern 6 12) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 6 12) else d23 (change pattern 6 12)) = d41 pattern
  rw [s5197, s5178]
  rfl
theorem s5199 (pattern : Twelve) : d815 (change pattern 6 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 6 12) else d9 (change pattern 6 12)) = d815 pattern
  rw [s5160, s5177]
  rfl
theorem s5200 (pattern : Twelve) : d820 (change pattern 6 12) = d820 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d815 (change pattern 6 12)) = d820 pattern
  rw [s5169, s5199]
  rfl
theorem s5201 (pattern : Twelve) : d829 (change pattern 6 12) = d829 pattern := by
  change (if pattern.h then d820 (change pattern 6 12) else d41 (change pattern 6 12)) = d829 pattern
  rw [s5200, s5198]
  rfl
theorem s5202 (pattern : Twelve) : d844 (change pattern 6 12) = d844 pattern := by
  change (if pattern.f then d829 (change pattern 6 12) else d59 (change pattern 6 12)) = d844 pattern
  rw [s5201, s5195]
  rfl
theorem s5203 (pattern : Twelve) : d40 (change pattern 6 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d23 (change pattern 6 12)) = d40 pattern
  rw [s5169, s5178]
  rfl
theorem s5204 (pattern : Twelve) : d830 (change pattern 6 12) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 6 12) else d41 (change pattern 6 12)) = d830 pattern
  rw [s5203, s5198]
  rfl
theorem s5205 (pattern : Twelve) : d13 (change pattern 6 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 6 12) else d4 (change pattern 6 12)) = d13 pattern
  rw [s5169, s5163]
  rfl
theorem s5206 (pattern : Twelve) : d14 (change pattern 6 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 6 12) else d5 (change pattern 6 12)) = d14 pattern
  rw [s5169, s5165]
  rfl
theorem s5207 (pattern : Twelve) : d21 (change pattern 6 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 6 12) else d13 (change pattern 6 12)) = d21 pattern
  rw [s5206, s5205]
  rfl
theorem s5208 (pattern : Twelve) : d821 (change pattern 6 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 6 12) else d25 (change pattern 6 12)) = d821 pattern
  rw [s5207, s5167]
  rfl
theorem s5209 (pattern : Twelve) : d822 (change pattern 6 12) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d21 (change pattern 6 12)) = d822 pattern
  rw [s5169, s5207]
  rfl
theorem s5210 (pattern : Twelve) : d831 (change pattern 6 12) = d831 pattern := by
  change (if pattern.h then d822 (change pattern 6 12) else d821 (change pattern 6 12)) = d831 pattern
  rw [s5209, s5208]
  rfl
theorem s5211 (pattern : Twelve) : d845 (change pattern 6 12) = d845 pattern := by
  change (if pattern.f then d831 (change pattern 6 12) else d830 (change pattern 6 12)) = d845 pattern
  rw [s5210, s5204]
  rfl
theorem s5212 (pattern : Twelve) : d856 (change pattern 6 12) = d856 pattern := by
  change (if pattern.e then d845 (change pattern 6 12) else d844 (change pattern 6 12)) = d856 pattern
  rw [s5211, s5202]
  rfl
theorem s5213 (pattern : Twelve) : d862 (change pattern 6 12) = d862 pattern := by
  change (if pattern.j then d856 (change pattern 6 12) else d855 (change pattern 6 12)) = d862 pattern
  rw [s5212, s5192]
  rfl
theorem s5214 (pattern : Twelve) : d863 (change pattern 6 12) = d863 pattern := by
  change (if pattern.j then d6 (change pattern 6 12) else d854 (change pattern 6 12)) = d863 pattern
  rw [s5169, s5186]
  rfl
theorem s5215 (pattern : Twelve) : d867 (change pattern 6 12) = d867 pattern := by
  change (if pattern.d then d863 (change pattern 6 12) else d862 (change pattern 6 12)) = d867 pattern
  rw [s5214, s5213]
  rfl
theorem s5216 (pattern : Twelve) : d869 (change pattern 6 12) = d869 pattern := by
  change (if pattern.c then d867 (change pattern 6 12) else d861 (change pattern 6 12)) = d869 pattern
  rw [s5215, s5187]
  rfl
theorem s5217 (pattern : Twelve) : d1268 (change pattern 6 12) = d869 pattern := by
  change d869 (change pattern 6 12) = d869 pattern
  exact s5216 pattern
theorem s5218 (pattern : Twelve) : d8 (change pattern 6 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 6 12) else d1 (change pattern 6 12)) = d8 pattern
  rw [s5158, s5150]
  rfl
theorem s5219 (pattern : Twelve) : d872 (change pattern 6 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 6 12) else d1 (change pattern 6 12)) = d872 pattern
  rw [s5218, s5150]
  rfl
theorem s5220 (pattern : Twelve) : d874 (change pattern 6 12) = d874 pattern := by
  change (if pattern.i then d872 (change pattern 6 12) else d17 (change pattern 6 12)) = d874 pattern
  rw [s5219, s5152]
  rfl
theorem s5221 (pattern : Twelve) : d875 (change pattern 6 12) = d875 pattern := by
  change (if pattern.i then d872 (change pattern 6 12) else d814 (change pattern 6 12)) = d875 pattern
  rw [s5219, s5154]
  rfl
theorem s5222 (pattern : Twelve) : d882 (change pattern 6 12) = d882 pattern := by
  change (if pattern.h then d875 (change pattern 6 12) else d874 (change pattern 6 12)) = d882 pattern
  rw [s5221, s5220]
  rfl
theorem s5223 (pattern : Twelve) : d890 (change pattern 6 12) = d890 pattern := by
  change (if pattern.f then d882 (change pattern 6 12) else d0 (change pattern 6 12)) = d890 pattern
  rw [s5222, s5149]
  rfl
theorem s5224 (pattern : Twelve) : d876 (change pattern 6 12) = d876 pattern := by
  change (if pattern.i then d21 (change pattern 6 12) else d19 (change pattern 6 12)) = d876 pattern
  rw [s5207, s5162]
  rfl
theorem s5225 (pattern : Twelve) : d883 (change pattern 6 12) = d883 pattern := by
  change (if pattern.h then d42 (change pattern 6 12) else d876 (change pattern 6 12)) = d883 pattern
  rw [s5170, s5224]
  rfl
theorem s5226 (pattern : Twelve) : d891 (change pattern 6 12) = d891 pattern := by
  change (if pattern.f then d883 (change pattern 6 12) else d17 (change pattern 6 12)) = d891 pattern
  rw [s5225, s5152]
  rfl
theorem s5227 (pattern : Twelve) : d898 (change pattern 6 12) = d898 pattern := by
  change (if pattern.e then d891 (change pattern 6 12) else d890 (change pattern 6 12)) = d898 pattern
  rw [s5226, s5223]
  rfl
theorem s5228 (pattern : Twelve) : d877 (change pattern 6 12) = d877 pattern := by
  change (if pattern.i then d815 (change pattern 6 12) else d17 (change pattern 6 12)) = d877 pattern
  rw [s5199, s5152]
  rfl
theorem s5229 (pattern : Twelve) : d884 (change pattern 6 12) = d884 pattern := by
  change (if pattern.h then d818 (change pattern 6 12) else d877 (change pattern 6 12)) = d884 pattern
  rw [s5180, s5228]
  rfl
theorem s5230 (pattern : Twelve) : d892 (change pattern 6 12) = d892 pattern := by
  change (if pattern.f then d884 (change pattern 6 12) else d56 (change pattern 6 12)) = d892 pattern
  rw [s5229, s5176]
  rfl
theorem s5231 (pattern : Twelve) : d893 (change pattern 6 12) = d893 pattern := by
  change (if pattern.f then d883 (change pattern 6 12) else d827 (change pattern 6 12)) = d893 pattern
  rw [s5225, s5184]
  rfl
theorem s5232 (pattern : Twelve) : d899 (change pattern 6 12) = d899 pattern := by
  change (if pattern.e then d893 (change pattern 6 12) else d892 (change pattern 6 12)) = d899 pattern
  rw [s5231, s5230]
  rfl
theorem s5233 (pattern : Twelve) : d902 (change pattern 6 12) = d902 pattern := by
  change (if pattern.j then d899 (change pattern 6 12) else d898 (change pattern 6 12)) = d902 pattern
  rw [s5232, s5227]
  rfl
theorem s5234 (pattern : Twelve) : d878 (change pattern 6 12) = d878 pattern := by
  change (if pattern.i then d24 (change pattern 6 12) else d814 (change pattern 6 12)) = d878 pattern
  rw [s5197, s5154]
  rfl
theorem s5235 (pattern : Twelve) : d885 (change pattern 6 12) = d885 pattern := by
  change (if pattern.h then d878 (change pattern 6 12) else d877 (change pattern 6 12)) = d885 pattern
  rw [s5234, s5228]
  rfl
theorem s5236 (pattern : Twelve) : d894 (change pattern 6 12) = d894 pattern := by
  change (if pattern.f then d885 (change pattern 6 12) else d30 (change pattern 6 12)) = d894 pattern
  rw [s5235, s5174]
  rfl
theorem s5237 (pattern : Twelve) : d117 (change pattern 6 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 6 12) else d3 (change pattern 6 12)) = d117 pattern
  rw [s5163, s5160]
  rfl
theorem s5238 (pattern : Twelve) : d119 (change pattern 6 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 6 12) else d3 (change pattern 6 12)) = d119 pattern
  rw [s5237, s5160]
  rfl
theorem s5239 (pattern : Twelve) : d879 (change pattern 6 12) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 6 12) else d17 (change pattern 6 12)) = d879 pattern
  rw [s5238, s5152]
  rfl
theorem s5240 (pattern : Twelve) : d886 (change pattern 6 12) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 6 12) else d34 (change pattern 6 12)) = d886 pattern
  rw [s5239, s5179]
  rfl
theorem s5241 (pattern : Twelve) : d895 (change pattern 6 12) = d895 pattern := by
  change (if pattern.f then d883 (change pattern 6 12) else d886 (change pattern 6 12)) = d895 pattern
  rw [s5225, s5240]
  rfl
theorem s5242 (pattern : Twelve) : d900 (change pattern 6 12) = d900 pattern := by
  change (if pattern.e then d895 (change pattern 6 12) else d894 (change pattern 6 12)) = d900 pattern
  rw [s5241, s5236]
  rfl
theorem s5243 (pattern : Twelve) : d22 (change pattern 6 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 6 12) else d14 (change pattern 6 12)) = d22 pattern
  rw [s5169, s5206]
  rfl
theorem s5244 (pattern : Twelve) : d127 (change pattern 6 12) = d127 pattern := by
  change (if pattern.i then d22 (change pattern 6 12) else d23 (change pattern 6 12)) = d127 pattern
  rw [s5243, s5178]
  rfl
theorem s5245 (pattern : Twelve) : d873 (change pattern 6 12) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 6 12) else d117 (change pattern 6 12)) = d873 pattern
  rw [s5196, s5237]
  rfl
theorem s5246 (pattern : Twelve) : d880 (change pattern 6 12) = d880 pattern := by
  change (if pattern.i then d6 (change pattern 6 12) else d873 (change pattern 6 12)) = d880 pattern
  rw [s5169, s5245]
  rfl
theorem s5247 (pattern : Twelve) : d887 (change pattern 6 12) = d887 pattern := by
  change (if pattern.h then d880 (change pattern 6 12) else d127 (change pattern 6 12)) = d887 pattern
  rw [s5246, s5244]
  rfl
theorem s5248 (pattern : Twelve) : d896 (change pattern 6 12) = d896 pattern := by
  change (if pattern.f then d887 (change pattern 6 12) else d59 (change pattern 6 12)) = d896 pattern
  rw [s5247, s5195]
  rfl
theorem s5249 (pattern : Twelve) : d118 (change pattern 6 12) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 6 12) else d5 (change pattern 6 12)) = d118 pattern
  rw [s5206, s5165]
  rfl
end NetHack.Sokoban21.Diagram
