/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5180 (p : Pattern) (guard : d4206 p = 1) : d131 p ≤ (0 : Int) + d1579 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d131, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d131, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d131, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5179 p hg
    simpa only [d131, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5181 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d336 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5182 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d1580 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d105, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d105, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d105, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5181 p hg
    simpa only [d4206, d105, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5183 (p : Pattern) (guard : d4206 p = 1) : d132 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4206, d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d4206, d132, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5184 (p : Pattern) (guard : d4206 p = 1) : d133 p ≤ (0 : Int) + d1581 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d133, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5182 p hg
    simpa only [d133, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d133, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d133, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5185 (p : Pattern) (guard : d4206 p = 1) : d134 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d134, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5186 (p : Pattern) (guard : d4206 p = 1) : d135 p ≤ (0 : Int) + d1582 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d135, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d135, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d135, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d135, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5187 (p : Pattern) (guard : d4206 p = 1) : d136 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d136, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5188 (p : Pattern) (guard : d4206 p = 1) : d137 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5187 p hg
    simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d137, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5189 (p : Pattern) (guard : d4206 p = 1) : d138 p ≤ (0 : Int) + d1583 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d138, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d138, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d138, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d138, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5190 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d139 p := by
  omega
theorem compare5191 (p : Pattern) (guard : d4206 p = 1) : d140 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d140, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d140, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d140, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d140, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5192 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (0 : Int) + d141 p := by
  omega
theorem compare5193 (p : Pattern) (guard : d4206 p = 1) : d142 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d142, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d142, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d142, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5192 p hg
    simpa only [d142, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5194 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare5195 (p : Pattern) (guard : d4206 p = 1) : d145 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d145, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5193 p hg
    simpa only [d145, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d145, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d145, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5196 (p : Pattern) (guard : d4206 p = 1) : d146 p ≤ (0 : Int) + d1587 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d146, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5189 p hg
    simpa only [d146, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d146, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d146, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5197 (p : Pattern) (guard : d4206 p = 1) : d147 p ≤ (0 : Int) + d1588 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d147, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5180 p hg
    simpa only [d147, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d147, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5196 p hg
    simpa only [d147, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5198 (p : Pattern) (guard : d4206 p = 1) : d111 p ≤ (0 : Int) + d1577 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d111, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d111, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d111, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d111, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5199 (p : Pattern) (guard : d4206 p = 1) : d114 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d114, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d114, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d114, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d114, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5200 (p : Pattern) (guard : d4206 p = 1) : d148 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d148, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4206, d148, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d148, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d4206, d148, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5201 (p : Pattern) (guard : d4206 p = 1) : d149 p ≤ (0 : Int) + d1053 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d149, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d149, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d149, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d149, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5202 (p : Pattern) (guard : d4206 p = 1) : d150 p ≤ (0 : Int) + d1054 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d150, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d150, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d150, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d150, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5203 (p : Pattern) (guard : d4206 p = 1) : d151 p ≤ (0 : Int) + d1589 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d151, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d151, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d151, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d151, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5204 (p : Pattern) (guard : d4206 p = 1) : d152 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d152, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d152, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d152, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d152, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5205 (p : Pattern) (guard : d4206 p = 1) : d133 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d133, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d133, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d133, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d133, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5206 (p : Pattern) (guard : d4206 p = 1) : d135 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d135, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d135, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d135, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d135, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5207 (p : Pattern) (guard : d4206 p = 1) : d138 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d138, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d138, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d138, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d138, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5208 (p : Pattern) (guard : d4206 p = 1) : d153 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d153, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d153, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d153, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d153, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5209 (p : Pattern) (guard : d4206 p = 1) : d154 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d154, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d154, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d154, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d154, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5210 (p : Pattern) (guard : d4206 p = 1) : d155 p ≤ (0 : Int) + d1591 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d155, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d155, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d155, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d155, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5211 (p : Pattern) (guard : d4206 p = 1) : d156 p ≤ (0 : Int) + d1592 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d156, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d156, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d156, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d156, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5212 (p : Pattern) (guard : d4206 p = 1) : d157 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d157, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d157, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d157, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d157, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5213 (p : Pattern) (guard : d4206 p = 1) : d158 p ≤ (0 : Int) + d1594 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d158, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d158, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d158, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d158, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5214 (p : Pattern) (guard : d4206 p = 1) : d159 p ≤ (0 : Int) + d1595 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d159, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d159, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d159, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d159, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5215 (p : Pattern) (guard : d4206 p = 1) : d160 p ≤ (0 : Int) + d1596 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5214 p hg
    simpa only [d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5216 (p : Pattern) (guard : d4206 p = 1) : d161 p ≤ (0 : Int) + d1597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5217 (p : Pattern) (guard : d4206 p = 1) : d162 p ≤ (0 : Int) + d1598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5216 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5218 (p : Pattern) (guard : d4206 p = 1) : d163 p ≤ (0 : Int) + d1599 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d163, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d163, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d163, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d163, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5219 (p : Pattern) (guard : d4206 p = 1) : d164 p ≤ (0 : Int) + d1600 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d164, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5213 p hg
    simpa only [d164, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d164, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d164, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5220 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d1601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5160 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5221 (p : Pattern) (guard : d4206 p = 1) : d111 p ≤ (0 : Int) + d1602 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d111, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5220 p hg
    simpa only [d111, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d111, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d111, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5222 (p : Pattern) (guard : d4206 p = 1) : d114 p ≤ (0 : Int) + d1603 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d114, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d114, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d114, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d114, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5223 (p : Pattern) (guard : d4206 p = 1) : d131 p ≤ (0 : Int) + d1604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d131, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d131, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d131, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5179 p hg
    simpa only [d131, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5224 (p : Pattern) (guard : d4206 p = 1) : d146 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5225 (p : Pattern) (guard : d4206 p = 1) : d147 p ≤ (0 : Int) + d1605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d147, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5223 p hg
    simpa only [d147, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d147, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5224 p hg
    simpa only [d147, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5226 (p : Pattern) (guard : d4206 p = 1) : d158 p ≤ (0 : Int) + d1606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d158, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5225 p hg
    simpa only [d158, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d158, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d158, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5227 (p : Pattern) (guard : d4206 p = 1) : d165 p ≤ (0 : Int) + d1607 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d165, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d165, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d165, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d165, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5228 (p : Pattern) (guard : d4206 p = 1) : d166 p ≤ (0 : Int) + d1608 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d166, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d166, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d166, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d166, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5229 (p : Pattern) (guard : d4206 p = 1) : d167 p ≤ (0 : Int) + d1609 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d167, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5219 p hg
    simpa only [d167, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d167, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5228 p hg
    simpa only [d167, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5230 (p : Pattern) (guard : d4206 p = 1) : d168 p ≤ (0 : Int) + d1610 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d168, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d168, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d168, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5229 p hg
    simpa only [d168, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5231 (p : Pattern) (guard : d4206 p = 1) : d169 p ≤ (0 : Int) + d1611 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d169, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5156 p hg
    simpa only [d169, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d169, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5230 p hg
    simpa only [d169, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5232 (p : Pattern) (guard : d4206 p = 1) : d170 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d4206, d170, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5233 (p : Pattern) (guard : d4206 p = 1) : d171 p ≤ (0 : Int) + d66 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5234 (p : Pattern) (guard : d4206 p = 1) : d172 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d172, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4206, d172, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d172, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d4206, d172, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5235 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (0 : Int) + d173 p := by
  omega
theorem compare5236 (p : Pattern) (guard : d4206 p = 1) : d174 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d174, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d174, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d174, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5235 p hg
    simpa only [d174, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5237 (p : Pattern) (guard : d4206 p = 1) : d175 p ≤ (0 : Int) + d1612 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d175, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d175, d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d175, d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5236 p hg
    simpa only [d175, d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5238 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (0 : Int) + d177 p := by
  omega
theorem compare5239 (p : Pattern) (guard : d4206 p = 1) : d178 p ≤ (0 : Int) + d1613 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d178, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5237 p hg
    simpa only [d178, d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d178, d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d178, d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5240 (p : Pattern) (guard : d4206 p = 1) : d179 p ≤ (0 : Int) + d1614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d179, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d179, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d179, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5239 p hg
    simpa only [d179, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5241 (p : Pattern) (guard : d4206 p = 1) : d180 p ≤ (0 : Int) + d1615 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d180, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d180, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d180, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d180, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5242 (p : Pattern) (guard : d4206 p = 1) : d181 p ≤ (0 : Int) + d181 p := by
  omega
theorem compare5243 (p : Pattern) (guard : d4206 p = 1) : d182 p ≤ (0 : Int) + d1616 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d182, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5241 p hg
    simpa only [d182, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d182, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5242 p hg
    simpa only [d182, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5244 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (0 : Int) + d184 p := by
  omega
theorem compare5245 (p : Pattern) (guard : d4206 p = 1) : d185 p ≤ (0 : Int) + d1617 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d185, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5243 p hg
    simpa only [d185, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d185, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5244 p hg
    simpa only [d185, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5246 (p : Pattern) (guard : d4206 p = 1) : d186 p ≤ (0 : Int) + d1618 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d186, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d186, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d186, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d186, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5247 (p : Pattern) (guard : d4206 p = 1) : d187 p ≤ (0 : Int) + d1619 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d187, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5240 p hg
    simpa only [d187, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d187, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5246 p hg
    simpa only [d187, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5248 (p : Pattern) (guard : d4206 p = 1) : d188 p ≤ (0 : Int) + d1620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d188, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d188, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d188, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5099 p hg
    simpa only [d188, d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5249 (p : Pattern) (guard : d4206 p = 1) : d189 p ≤ (0 : Int) + d1621 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d189, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5248 p hg
    simpa only [d189, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d189, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5100 p hg
    simpa only [d189, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5250 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (0 : Int) + d191 p := by
  omega
theorem compare5251 (p : Pattern) (guard : d0 p = 1) : d192 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5252 (p : Pattern) (guard : d4206 p = 1) : d193 p ≤ (0 : Int) + d1622 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d193, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d4206, d193, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d193, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5251 p hg
    simpa only [d4206, d193, d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5253 (p : Pattern) (guard : d4206 p = 1) : d194 p ≤ (0 : Int) + d1623 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d194, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d194, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d194, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d194, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5254 (p : Pattern) (guard : d4206 p = 1) : d195 p ≤ (0 : Int) + d1624 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d195, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5253 p hg
    simpa only [d195, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d195, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d195, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5255 (p : Pattern) (guard : d4206 p = 1) : d196 p ≤ (0 : Int) + d1625 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d196, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5254 p hg
    simpa only [d196, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d196, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d196, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5256 (p : Pattern) (guard : d4206 p = 1) : d197 p ≤ (0 : Int) + d1626 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d197, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d197, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d197, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5255 p hg
    simpa only [d197, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5257 (p : Pattern) (guard : d4206 p = 1) : d198 p ≤ (0 : Int) + d1627 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d198, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d198, d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d198, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d198, d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5258 (p : Pattern) (guard : d4206 p = 1) : d199 p ≤ (0 : Int) + d1628 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d199, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d199, d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d199, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5257 p hg
    simpa only [d199, d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5259 (p : Pattern) (guard : d4206 p = 1) : d200 p ≤ (0 : Int) + d1629 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d200, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5258 p hg
    simpa only [d200, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d200, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5107 p hg
    simpa only [d200, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5260 (p : Pattern) (guard : d4206 p = 1) : d201 p ≤ (0 : Int) + d1630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d201, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d201, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d201, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d201, d1630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5261 (p : Pattern) (guard : d4206 p = 1) : d202 p ≤ (0 : Int) + d1631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d202, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5260 p hg
    simpa only [d202, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d202, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d202, d1631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5262 (p : Pattern) (guard : d4206 p = 1) : d203 p ≤ (0 : Int) + d1632 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d203, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5261 p hg
    simpa only [d203, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d203, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d203, d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5263 (p : Pattern) (guard : d4206 p = 1) : d204 p ≤ (0 : Int) + d1633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d204, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5259 p hg
    simpa only [d204, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d204, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5262 p hg
    simpa only [d204, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5264 (p : Pattern) (guard : d4206 p = 1) : d205 p ≤ (0 : Int) + d1634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d205, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5256 p hg
    simpa only [d205, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d205, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5263 p hg
    simpa only [d205, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5265 (p : Pattern) (guard : d4206 p = 1) : d206 p ≤ (0 : Int) + d1635 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d206, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5247 p hg
    simpa only [d206, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d206, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5264 p hg
    simpa only [d206, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5266 (p : Pattern) (guard : d4206 p = 1) : d207 p ≤ (0 : Int) + d1636 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d207, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5264 p hg
    simpa only [d207, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d207, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d207, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5267 (p : Pattern) (guard : d4206 p = 1) : d208 p ≤ (0 : Int) + d1637 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d208, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5265 p hg
    simpa only [d208, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d208, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5266 p hg
    simpa only [d208, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5268 (p : Pattern) (guard : d4206 p = 1) : d209 p ≤ (0 : Int) + d1638 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d209, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d209, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d209, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5267 p hg
    simpa only [d209, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5269 (p : Pattern) (guard : d4206 p = 1) : d210 p ≤ (0 : Int) + d1639 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d210, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d210, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d210, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5268 p hg
    simpa only [d210, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5270 (p : Pattern) (guard : d4206 p = 1) : d211 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d211, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5271 (p : Pattern) (guard : d4206 p = 1) : d212 p ≤ (0 : Int) + d1640 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d212, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d212, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d212, d1640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d212, d1640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5272 (p : Pattern) (guard : d4206 p = 1) : d213 p ≤ (0 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d213, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5273 (p : Pattern) (guard : d4206 p = 1) : d214 p ≤ (0 : Int) + d1641 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d214, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d214, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d214, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d214, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5274 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (0 : Int) + d215 p := by
  omega
theorem compare5275 (p : Pattern) (guard : d4206 p = 1) : d216 p ≤ (0 : Int) + d1642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d216, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d216, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d216, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d216, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5276 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (0 : Int) + d217 p := by
  omega
theorem compare5277 (p : Pattern) (guard : d4206 p = 1) : d218 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d218, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5275 p hg
    simpa only [d218, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d218, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5276 p hg
    simpa only [d218, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5278 (p : Pattern) (guard : d4206 p = 1) : d219 p ≤ (0 : Int) + d1644 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d219, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d219, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d219, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d219, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5279 (p : Pattern) (guard : d4206 p = 1) : d220 p ≤ (0 : Int) + d1645 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d220, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5180 p hg
    simpa only [d220, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d220, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d220, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5280 (p : Pattern) (guard : d4206 p = 1) : d212 p ≤ (0 : Int) + d1642 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d212, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d212, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d212, d1642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d212, d1642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5281 (p : Pattern) (guard : d4206 p = 1) : d214 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d214, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d214, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d214, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d214, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5282 (p : Pattern) (guard : d4206 p = 1) : d221 p ≤ (0 : Int) + d1646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d221, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d221, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d221, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d221, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5283 (p : Pattern) (guard : d4206 p = 1) : d222 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d222, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d222, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d222, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d222, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5284 (p : Pattern) (guard : d4206 p = 1) : d223 p ≤ (0 : Int) + d1648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d223, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d223, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d223, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d223, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5285 (p : Pattern) (guard : d4206 p = 1) : d224 p ≤ (0 : Int) + d1649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d224, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d224, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d224, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d224, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5286 (p : Pattern) (guard : d4206 p = 1) : d225 p ≤ (0 : Int) + d1650 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d225, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d225, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d225, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d225, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5287 (p : Pattern) (guard : d4206 p = 1) : d226 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d226, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4206, d226, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d226, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d4206, d226, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5288 (p : Pattern) (guard : d4206 p = 1) : d227 p ≤ (0 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5289 (p : Pattern) (guard : d4206 p = 1) : d228 p ≤ (0 : Int) + d1651 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d228, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5288 p hg
    simpa only [d228, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d228, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d228, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5290 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (0 : Int) + d231 p := by
  omega
theorem compare5291 (p : Pattern) (guard : d4206 p = 1) : d232 p ≤ (0 : Int) + d1652 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d232, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d232, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d232, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d232, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5292 (p : Pattern) (guard : d4206 p = 1) : d233 p ≤ (0 : Int) + d1653 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d233, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d233, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d233, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d233, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5293 (p : Pattern) (guard : d4206 p = 1) : d234 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d234, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4206, d234, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d234, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d4206, d234, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5294 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  omega
theorem compare5295 (p : Pattern) (guard : d4206 p = 1) : d235 p ≤ (0 : Int) + d125 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5296 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (0 : Int) + d230 p := by
  omega
theorem compare5297 (p : Pattern) (guard : d4206 p = 1) : d236 p ≤ (0 : Int) + d1654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d236, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d236, d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d236, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d236, d1654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5298 (p : Pattern) (guard : d4206 p = 1) : d237 p ≤ (0 : Int) + d237 p := by
  omega
theorem compare5299 (p : Pattern) (guard : d4206 p = 1) : d238 p ≤ (0 : Int) + d1655 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d238, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5297 p hg
    simpa only [d238, d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d238, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d238, d1655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5300 (p : Pattern) (guard : d4206 p = 1) : d239 p ≤ (0 : Int) + d1656 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d239, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d239, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d239, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5299 p hg
    simpa only [d239, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5301 (p : Pattern) (guard : d4206 p = 1) : d240 p ≤ (0 : Int) + d1657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d240, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5292 p hg
    simpa only [d240, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d240, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5300 p hg
    simpa only [d240, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5302 (p : Pattern) (guard : d4206 p = 1) : d241 p ≤ (0 : Int) + d1658 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d241, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d241, d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d241, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d241, d1658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5303 (p : Pattern) (guard : d4206 p = 1) : d242 p ≤ (0 : Int) + d1659 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d242, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d242, d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d242, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5302 p hg
    simpa only [d242, d1659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5304 (p : Pattern) (guard : d4206 p = 1) : d243 p ≤ (0 : Int) + d1660 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d243, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d243, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d243, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d243, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5305 (p : Pattern) (guard : d4206 p = 1) : d244 p ≤ (0 : Int) + d1661 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d244, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d244, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d244, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d244, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5306 (p : Pattern) (guard : d4206 p = 1) : d245 p ≤ (0 : Int) + d1651 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d245, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d245, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d245, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d245, d1651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5307 (p : Pattern) (guard : d4206 p = 1) : d246 p ≤ (0 : Int) + d1652 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d246, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5306 p hg
    simpa only [d246, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d246, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d246, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5308 (p : Pattern) (guard : d4206 p = 1) : d247 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d247, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d247, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d247, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d247, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5309 (p : Pattern) (guard : d4206 p = 1) : d248 p ≤ (0 : Int) + d1662 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d248, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d248, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d248, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d248, d1662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5310 (p : Pattern) (guard : d4206 p = 1) : d249 p ≤ (0 : Int) + d1663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d249, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d249, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d249, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d249, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5311 (p : Pattern) (guard : d4206 p = 1) : d250 p ≤ (0 : Int) + d1664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d250, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d250, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d250, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d250, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5312 (p : Pattern) (guard : d4206 p = 1) : d251 p ≤ (0 : Int) + d1665 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d251, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d251, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d251, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d251, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5313 (p : Pattern) (guard : d4206 p = 1) : d252 p ≤ (0 : Int) + d1666 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d252, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d252, d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d252, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d252, d1666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5314 (p : Pattern) (guard : d4206 p = 1) : d253 p ≤ (0 : Int) + d1667 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d253, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d253, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d253, d1667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d253, d1667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5315 (p : Pattern) (guard : d4206 p = 1) : d254 p ≤ (0 : Int) + d1668 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d254, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d254, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d254, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d254, d1668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5316 (p : Pattern) (guard : d4206 p = 1) : d255 p ≤ (0 : Int) + d1669 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d255, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5315 p hg
    simpa only [d255, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d255, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d255, d1669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5317 (p : Pattern) (guard : d4206 p = 1) : d256 p ≤ (0 : Int) + d1670 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d256, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d256, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d256, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5316 p hg
    simpa only [d256, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5318 (p : Pattern) (guard : d4206 p = 1) : d257 p ≤ (0 : Int) + d1671 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d257, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d257, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d257, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d257, d1671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5319 (p : Pattern) (guard : d4206 p = 1) : d258 p ≤ (0 : Int) + d1672 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d258, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5318 p hg
    simpa only [d258, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d258, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d258, d1672, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
